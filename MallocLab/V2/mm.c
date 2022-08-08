/*
 * mm.c -  PHASE II - implemented explicit Free List 

 *         Not so simple allocator based on explicit free lists,
 *         first fit placement, and boundary tag coalescing.
 *
 * Each block has header and footer of the form:
 *
 *      63       32   31        1   0
 *      --------------------------------
 *     |   unused   | block_size | a/f |
 *      --------------------------------
 *
 * a/f is 1 iff the block is allocated. The list has the following form:
 *
 * begin                                       end
 * heap                                       heap
 *  ----------------------------------------------
 * | hdr(8:a) | zero or more usr blks | hdr(0:a) |
 *  ----------------------------------------------
 * | prologue |                       | epilogue |
 * | block    |                       | block    |
 *
 * The allocated prologue and epilogue blocks are overhead that
 * eliminate edge conditions during coalescing.
 */

/* 
    LIFE LESSONS: 
    1. DO NOT EVER GIVE THE SAME NAME TO A LOCAL VARIABLE AS ONE OF THE FIELDS IN THE STRUCT
    2. ALWAYS compile a file first before debug it, otherwise the version will be stuck
*/

#include "memlib.h"
#include "mm.h"
#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

/* Your info */
team_t team = {
    /* First and last name */
    "Harvey Zhao",
    /* UID */
    "405824231",
    /* Custom message (16 chars) */
    "Dawg",
};

typedef struct {
    uint32_t allocated : 1;
    uint32_t block_size : 31;
    uint32_t _;
} header_t;

typedef header_t footer_t;

typedef struct {
    uint32_t allocated : 1;
    uint32_t block_size : 31;
    uint32_t _;
    union {
        struct {
            struct block_t* next;
            struct block_t* prev;
        };
        int payload[0]; 
    } body; //What's the alignment requirement and memory requirement of body
} block_t;

/* This enum can be used to set the allocated bit in the block */
enum block_state { FREE,
                   ALLOC };


/* Macros */

#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE (1 << 16) /* initial heap size (bytes) */
#define OVERHEAD (sizeof(header_t) + sizeof(footer_t)) /* overhead of the header and footer of an allocated block */
#define MIN_BLOCK_SIZE (32) /* the minimum block size needed to keep in a freelist (header + footer + next pointer + prev pointer) */

#define MAX(x,y) ((x) > (y) ? (x) : (y))

#define PACK(p, size, alloc)    ((p)->block_size = size, (p)->allocated = alloc)
#define PREV(p, prv)   ((p->body).prev = (void *)prv)  
#define NEXT(p, nxt)   ((p->body).next = (void *)nxt)

/* Read and write a word at address p */
#define GET(p)  (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (((block_t *)(p))->block_size)    //get size in BYTES
#define GET_ALLOC(p) (((block_t *)(p))->allocated)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)    (header_t *)((void *)(bp))    
#define FTRP(bp)    (footer_t *)((void *)(bp) + GET_SIZE(HDRP(bp)) - sizeof(header_t))  // ADD (VOID *) if an error pops up
#define PLDP(bp)    ((void *)(bp) + sizeof(header_t))   //accessing PAYLOAD in allocated blocks
#define NXTP(bp)    ((void *)(bp) + sizeof(header_t))   //accessing NEXT pointer in free blocks
#define PRVP(bp)    ((void *)(bp) + sizeof(header_t) + sizeof(root))    //accessing PREV pointer in free blocks

/* Given block ptr bp, compute address of next and previous blocks */
#define PREV_FTRP(bp)   ((void *)block - sizeof(header_t))
#define NEXT_BLKP(bp)   ((void *)(bp) + GET_SIZE(bp))  //points to the beginning of the block, not the payload
#define PREV_BLKP(bp)   ((void *)(bp) - GET_SIZE(PREV_FTRP(bp)))

/* Checking purposes */
#define CHK_ALN(bp)     (((uint64_t)PLDP(bp)) % 8)  //if aligned to DSIZE, return 0

/* Global variables */
static block_t *prologue; /* pointer to first block */
static block_t *m_root = NULL;    /* root of the explicit free list */
static block_t *m_tail = NULL;    /* tail of the explicit free list */

/* function prototypes for internal helper routines */
static block_t *extend_heap(size_t words);
static void place(block_t *block, size_t asize);
static block_t *find_fit(size_t asize);
static block_t *coalesce(block_t *block);
static footer_t *get_footer(block_t *block);
static void printblock(block_t *block);
static void checkblock(block_t *block);
static void checklist(void);
static void insertBlock(block_t *block);
static void removeBlock(block_t *block);
void mm_checkheap(int verbose);


/*
 * mm_init - Initialize the memory manager
 */
/* $begin mminit */
int mm_init(void) { 
    /* create the initial empty heap */
    // printf("INITIAL HI = %p\n", mem_heap_hi());
    if ((prologue = mem_sbrk(CHUNKSIZE)) == (void*)-1)
        return -1;

    // printf("EXPANDED HI = %p\n", mem_heap_hi());
    /* initialize the prologue */
    PACK(prologue, sizeof(header_t), ALLOC);
    
    // /* initialize CHUNKSPACE */
    block_t *init_block = NEXT_BLKP(prologue);
    PACK(HDRP(init_block), (CHUNKSIZE - OVERHEAD), FREE);
    PACK(FTRP(init_block), (CHUNKSIZE - OVERHEAD), FREE);
    insertBlock(init_block);

    // /* initialize EPILOGUE */
    block_t *epilogue = NEXT_BLKP(init_block);
    PACK(HDRP(epilogue), 0, ALLOC);
    // mm_checkheap(0);
    return 0;
}
/* $end mminit */

/*
 * mm_malloc - Allocate a block with at least size bytes of payload
 */
/* $begin mmmalloc */
void *mm_malloc(size_t size) {
    uint32_t asize;       /* adjusted block size */
    uint32_t extendsize;  /* amount to extend heap if no fit */
    uint32_t extendwords; /* number of words to extend heap if no fit */
    block_t *block;

    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    size += OVERHEAD;
    asize = ((size + 7) >> 3) << 3; /* IMPORTANT ALIGNMENT FORMULA: align to multiple of 8 */
    if (asize < MIN_BLOCK_SIZE) {
        asize = MIN_BLOCK_SIZE;
    }

    /* Search the free list for a fit */
    if ((block = find_fit(asize)) != NULL) {
        place(block, asize);
        // mm_checkheap(0);
        return PLDP(block);
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    extendwords = extendsize >> 3; // extendsize/8
    if ((block = extend_heap(extendwords)) != NULL) {
        place(block, asize);
        // mm_checkheap(0);
        return block->body.payload;
    }
    
    /* no more memory :( */
    // mm_checkheap(0);
    return NULL;
}
/* $end mmmalloc */


/*
 * mm_free - Free a block
 */
/* $begin mmfree */
void mm_free(void *payload) {
    /* Free the block first */
    block_t *bp = payload - sizeof(header_t);
    PACK(HDRP(bp), GET_SIZE(bp), FREE);
    PACK(FTRP(bp), GET_SIZE(bp), FREE);
    
    /* Coalesce */
    coalesce(bp);

    /* TODO: delete when finished developing */
    // mm_checkheap(0);
}
/* $end mmfree */


/*
 * mm_realloc - naive implementation of mm_realloc
 * NO NEED TO CHANGE THIS CODE!
 */
void *mm_realloc(void *ptr, size_t size) {
    void *newp;
    size_t copySize;

    if ((newp = mm_malloc(size)) == NULL) {
        printf("ERROR: mm_malloc failed in mm_realloc\n");
        exit(1);
    }
    block_t* block = ptr - sizeof(header_t);
    copySize = block->block_size;
    if (size < copySize)
        copySize = size;
    memcpy(newp, ptr, copySize);
    mm_free(ptr);
    return newp;
}


/*
 * mm_checkheap - Check the heap for consistency
 */

void mm_checkheap(int verbose) {
    block_t *bp = prologue;

    /* Check Prologue */
    if (verbose)
        printf("Heap (%p):\n", prologue);
    if (GET_SIZE(bp) != sizeof(header_t) || !GET_ALLOC(bp))
        printf("Bad prologue header\n");
    checkblock(prologue);

    /* Check middle */
    for (bp = NEXT_BLKP(prologue); GET_SIZE(bp) > 0; bp = NEXT_BLKP(bp)) {
        if (verbose)
            printblock(bp);
        checkblock(bp);
    }

    /* Check Epilogue TODO: do not checkblock()*/
    if (verbose)
        printblock(bp);
    if (GET_SIZE(bp) != 0 || !GET_ALLOC(bp))
        printf("Bad epilogue header, epilogue size = %d, epilogue Allocation status = %d \n", GET_SIZE(bp), GET_ALLOC(bp));
    
    checklist();
}

/* The remaining routines are internal helper routines */

/*
 * extend_heap - Extend heap with free block and return its block pointer
 */
/* $begin mmextendheap */
static block_t *extend_heap(size_t words) {
    block_t *newChunkSpace;
    uint32_t size;

    size = words << 3; // words*8
    if (size == 0 || (newChunkSpace = mem_sbrk(size)) == (void *)-1)
        return NULL;

    /* The newly acquired region will start directly after the epilogue block */ 
    /* Initialize free block header/footer and the new epilogue header */
    newChunkSpace = (void *)newChunkSpace - sizeof(header_t);   /* use old epilogue as new free block header */
    PACK(HDRP(newChunkSpace), size, FREE);
    PACK(FTRP(newChunkSpace), size, FREE);

    /* new epilogue header */
    header_t *new_epilogue = NEXT_BLKP(newChunkSpace);
    PACK(new_epilogue, 0, ALLOC);

    // insertBlock(newChunkSpace);
    /* Coalesce if the previous block was free */
    return coalesce(newChunkSpace);
}
/* $end mmextendheap */

/* 
 * insertBlock - insert a free block into the free list
 */
/* $begin insertBlock */
static void insertBlock(block_t *block) {
    if (m_root == NULL)
    {
        if (m_tail != NULL)
        {
            printf("FORGOT TO CLEANUP tailptr\n"); 
            return;
        }
        block->body.prev = NULL;
        block->body.next = NULL;
        m_root = (void *)block;
        m_tail = (void *)block;
    } else {    //TODO: write a macro to encapsulate after testing
        m_root->body.prev = (void *)block;
        block->body.next = (void *)m_root;
        m_root = (void *)block;
        m_root->body.prev = NULL;
        m_tail->body.next = NULL;
    }
}

/* 
 * removeBlock - remove a free block from the free list
 */
/* $begin insertBlock */
static void removeBlock(block_t *block) {
    if (block == NULL)
    {
        printf("Error: removing a NULL block\n");
        return;
    }

    /* case 1. empty list*/
    if (m_root == NULL)
    {
        if (m_tail != NULL)
        {
            printf("FORGOT TO CLEANUP tailptr\n"); 
            return;
        }
        printf("Error: removing block in an empty list\n");
        return;
    }

    /* case 2. one-element list */
    else if (m_root == m_tail)
    {
        if (block != m_root || block != m_tail)
        {
            printf("Error: block not in one-element list\n");
            return;
        }
        m_root = NULL; 
        m_tail = NULL;
        block->body.prev = NULL;
        block->body.next = NULL;
    }

    /* case 3. head */
    else if (block == (void *)m_root)
    {
        m_root = (void *)(m_root->body.next);
        m_root->body.prev = NULL;
        block->body.prev = NULL;
        block->body.next = NULL;
    }

    /* case 4. tail */
    else if (block == (void *)m_tail)
    {
        m_tail = (void *)(m_tail->body.prev);
        m_tail->body.next = NULL;
        block->body.prev = NULL;
        block->body.next = NULL;
    }

    /* case 5. middle */
    else 
    {
        block_t *predptr = (void *)(block->body.prev);
        block_t *succptr = (void *)(block->body.next);

        predptr->body.next = (void *)(succptr);
        succptr->body.prev = (void *)(predptr);
        block->body.next = NULL;
        block->body.prev = NULL;
    }
}



/*
 * place - Place block of asize bytes at start of free block block
 *         and split if remainder would be at least minimum block size
 */
/* $begin mmplace */
static void place(block_t *block, size_t asize) {
    uint32_t split_size = GET_SIZE(block) - asize;

    if (split_size < MIN_BLOCK_SIZE) {
        // printf("placing block: WHOLE\n");
        PACK(HDRP(block), GET_SIZE(block), ALLOC);
        PACK(FTRP(block), GET_SIZE(block), ALLOC);
        removeBlock(block);
    } 
    
    else {
        // printf("placing block: SPLIT\n");
        removeBlock(block);
        block->block_size = asize;
        block->allocated = ALLOC;
        footer_t *m_footer = get_footer(block);
        m_footer->block_size = asize;
        m_footer->allocated = ALLOC;

        block_t *splitBlock = (void *)(NEXT_BLKP(block));
        splitBlock->block_size = split_size;
        splitBlock->allocated = FREE;
        footer_t *splitBlock_footer = get_footer(splitBlock);
        splitBlock_footer->block_size = split_size;
        splitBlock_footer->allocated = FREE;
        // PACK(HDRP(block), asize, ALLOC);    /* split the block by updating the header and marking it allocated*/
        // PACK(FTRP(block), asize, ALLOC);    /* set footer of allocated block*/

        insertBlock(splitBlock);
    }

    /* TODO: delete when finished developing */
    // mm_checkheap(0);
}
/* $end mmplace */

//TODO: try to employ best-fit search
/*
 * find_fit - Find a fit for a block with asize bytes
 */
static block_t *find_fit(size_t asize) {
    /* first fit search */
    block_t *block = (void *)m_root;

    while (block != NULL)
    {
        if (GET_SIZE(block) >= asize)
            return block;
        block = (void *)block->body.next;
    }
    return NULL; /* no fit */
}

/*
 * coalesce - boundary tag coalescing. Return ptr to coalesced block
 */
static block_t *coalesce(block_t *block) {
    if (block == NULL)
    {
        printf("Error: coalescing a NULLPTR\n");
        return NULL;
    }

    bool prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(block)));
    bool next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(block)));
    size_t size = GET_SIZE(block);

    /* case I: A | T | A */
    if (prev_alloc && next_alloc)
    {
        insertBlock(block);
        return block;
    }
        
    /* case II: A | T | F */
    else if (prev_alloc && !next_alloc)
    {
        //merge currBlk + nextBlk
        block_t *nextBlk = (void *)NEXT_BLKP(block);
        removeBlock(nextBlk);
        
        size += GET_SIZE(NEXT_BLKP(block));
        PACK(block, size, FREE);
        PACK(FTRP(block), size, FREE);
        insertBlock(block);
        return block;
    }

    /* Case III: F | T | A */
    else if (!prev_alloc && next_alloc) {
        //merge prevBlk + currBlk
        block_t *prevblk = (void *)PREV_BLKP(block);
        removeBlock(prevblk);

        size += GET_SIZE(FTRP(prevblk));
        PACK(FTRP(block), size, FREE);
        PACK(prevblk, size, FREE);  //FIXME: these may invoke seg fault because we rewrote the blocks

        insertBlock(prevblk);
        return prevblk;
    }

    /* case IV: F | T | F */
    else {
        block_t *prevblk = (void *)PREV_BLKP(block);
        block_t *nextblk = (void *)NEXT_BLKP(block);
        removeBlock(prevblk);
        removeBlock(nextblk);
        size += (GET_SIZE(prevblk) + GET_SIZE(nextblk));
        
        PACK(FTRP(nextblk), size, FREE);
        PACK(prevblk, size, FREE);
        insertBlock(prevblk);
        return prevblk;
    }
}

static footer_t* get_footer(block_t *block) {
    return (void*)block + block->block_size - sizeof(footer_t);
}

static void printblock(block_t *block) {
    uint32_t hsize, halloc, fsize, falloc;

    hsize = block->block_size;
    halloc = block->allocated;
    footer_t *footer = get_footer(block);
    fsize = footer->block_size;
    falloc = footer->allocated;

    if (hsize == 0) {
        printf("%p: EOL\n", block);
        return;
    }

    printf("%p: header: [%d:%c] footer: [%d:%c]\n", block, hsize,
           (halloc ? 'a' : 'f'), fsize, (falloc ? 'a' : 'f'));
}

static void checkblock(block_t *block) {
    // • Is every block in the free list marked as free?
    // • Is every free block actually in the free list?
    // • Do the pointers in the free list point to valid free blocks?
    // • Do the pointers in a heap block point to valid heap addresses? HINT: use mem_heap_lo and mem_heap_hi()

    // • Are there any contiguous free blocks that somehow escaped coalescing? 
    // • Do any allocated blocks overlap?   ALREADY CHECKED BY mdriver

    if (CHK_ALN(block)) {
        printf("Error: payload for block at %p is not aligned\n", block);
    }

    if (GET_SIZE(HDRP(block)) != GET_SIZE(FTRP(block))) {   //DOES NOT APPLY TO EPILOGUE!!! FTRP IS RIGGED
        printf("Error: header size does not match footer\n");
    }

    if (GET_ALLOC(HDRP(block)) != GET_ALLOC(FTRP(block))) {   //DOES NOT APPLY TO EPILOGUE!!! FTRP IS RIGGED
        printf("Error: header alloc does not match footer\n");
    }

    if (!GET_ALLOC(block) && !GET_ALLOC(NEXT_BLKP(block)))
    {
        printf("Error: free blocks at %p, %p escaped coalescing\n", 
                block, NEXT_BLKP(block));
    }
}

static void checklist(void) {
    block_t *block = (void *)m_root;

    /* check overall structure */
    if ((m_root == NULL && m_tail != NULL) || (m_root != NULL && m_tail == NULL))
    {
        printf("Error: m_root and m_tail is not synchronized.\n");
        return;
    }

    if ((void *)m_root == NULL)
        return;
    
    block_t *prv = (void *)(block->body.prev);
    block_t *nxt = (void *)(block->body.next);

    /* check root */
    if ((void *)prv != NULL)
    {
        printf("Error: root has non-NULL PREVptr\n");
    }

    /* check middle */
    while ((void *)block != m_tail)
    {
        prv = (void *)(block->body.prev);
        nxt = (void *)(block->body.next);

        if ((void *)block < mem_heap_lo() || (void *)(FTRP(block)) < mem_heap_lo())
        {
            printf("block b4 loheap\n");
        }

        if ((void *)(block) > mem_heap_hi() || (void *)(FTRP(block)) > mem_heap_hi())
        {
            printf("block above hiheap\n");
        }

        block = (void *)nxt;
    }

    nxt = (void *)(block->body.next);
    if ((void *)nxt != NULL)
    {
        printf("Error: tail has non-NULL NEXTptr\n");
    }
}
