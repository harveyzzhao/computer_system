/*
 * mm.c -  PHASE I - modified implicit Free List 

 *         Simple allocator based on implicit free lists,
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
            struct block_t* next;  //TODO: I changed struct block_t* to block_t*
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
static block_t *m_root;    /* root of the explicit free list */

/* function prototypes for internal helper routines */
static block_t *extend_heap(size_t words);
static void place(block_t *block, size_t asize);
static block_t *find_fit(size_t asize);
static block_t *coalesce(block_t *block);
static footer_t *get_footer(block_t *block);
static void printblock(block_t *block);
static void checkblock(block_t *block);
void mm_checkheap(int verbose);

/*
 * mm_init - Initialize the memory manager
 */
/* $begin mminit */
int mm_init(void) { //TODO: set up the root node
    /* create the initial empty heap */
    if ((prologue = mem_sbrk(CHUNKSIZE)) == (void*)-1)
        return -1;

    /* initialize the prologue */
    PACK(prologue, sizeof(header_t), ALLOC);
    
    // /* initialize CHUNKSPACE */
    block_t *init_block = NEXT_BLKP(prologue);
    PACK(HDRP(init_block), (CHUNKSIZE - OVERHEAD), FREE);
    PACK(FTRP(init_block), (CHUNKSIZE - OVERHEAD), FREE);

    // /* initialize EPILOGUE */
    block_t *epilogue = NEXT_BLKP(init_block);
    PACK(HDRP(epilogue), 0, ALLOC);
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
        return PLDP(block);
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    extendwords = extendsize >> 3; // extendsize/8
    if ((block = extend_heap(extendwords)) != NULL) {
        place(block, asize);
        return block->body.payload;
    }
    /* no more memory :( */
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
    mm_checkheap(0);
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

    /* Check Epilogue */
    if (verbose)
        printblock(bp);
    if (GET_SIZE(bp) != 0 || !GET_ALLOC(bp))
        printf("Bad epilogue header, epilogue size = %d, epilogue Allocation status = %d \n", GET_SIZE(bp), GET_ALLOC(bp));
}

/* The remaining routines are internal helper routines */

/*
 * extend_heap - Extend heap with free block and return its block pointer
 */
/* $begin mmextendheap */
static block_t *extend_heap(size_t words) {
    block_t *newChunkSpace;
    uint32_t size;

    size = words << 4; // words*8
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

    /* Coalesce if the previous block was free */
    return coalesce(newChunkSpace);
}
/* $end mmextendheap */

/* 
 * insertBlock - insert a free block into the free list
 */
/* $begin insertBlock */
static void insertBlock(block_t *block) {

}

/* 
 * removeBlock - remove a free block from the free list
 */
/* $begin insertBlock */
static void removeBlock(block_t *block) {

}



/*
 * place - Place block of asize bytes at start of free block block
 *         and split if remainder would be at least minimum block size
 */
/* $begin mmplace */
static void place(block_t *block, size_t asize) {
    size_t split_size = GET_SIZE(block) - asize;

    if (split_size < MIN_BLOCK_SIZE) {
        PACK(HDRP(block), GET_SIZE(block), ALLOC);
        PACK(FTRP(block), GET_SIZE(block), ALLOC);
    } else {
        PACK(HDRP(block), asize, ALLOC);    /* split the block by updating the header and marking it allocated*/
        PACK(FTRP(block), asize, ALLOC);    /* set footer of allocated block*/

        block = NEXT_BLKP(block);   //traverse to the split free block
        PACK(HDRP(block), split_size, FREE);    /* update the header of the new free block */
        PACK(FTRP(block), split_size, FREE);    /* update the footer of the new free block */
    }

    /* TODO: delete when finished developing */
    mm_checkheap(0);
}
/* $end mmplace */

//TODO: try to employ best-fit search
/*
 * find_fit - Find a fit for a block with asize bytes
 */
static block_t *find_fit(size_t asize) {
    /* first fit search */
    block_t *bp;

    for (bp = NEXT_BLKP(prologue); GET_SIZE(bp) > 0; bp = NEXT_BLKP(bp)) {
        /* block must be free and the size must be large enough to hold the request */
        if (!GET_ALLOC(bp) && asize <= GET_SIZE(bp))
            return bp;
    }
    return NULL; /* no fit */
}

/*
 * coalesce - boundary tag coalescing. Return ptr to coalesced block
 */
static block_t *coalesce(block_t *block) {
    bool prev_alloc = GET_ALLOC(PREV_BLKP(block));
    bool next_alloc = GET_ALLOC(NEXT_BLKP(block));
    size_t size = GET_SIZE(block);

    /* case I: A | T | A */
    if (prev_alloc && next_alloc)
        return block;

    /* case II: A | T | F */
    else if (prev_alloc && !next_alloc)
    {
        //merge currBlk + nextBlk
        size += GET_SIZE(NEXT_BLKP(block));
        PACK(HDRP(block), size, FREE);
        PACK(FTRP(block), size, FREE);
    }

    /* Case III: F | T | A */
    else if (!prev_alloc && next_alloc) {
        //merge prevBlk + currBlk
        size += GET_SIZE(PREV_BLKP(block));
        block = PREV_BLKP(block);
        PACK(HDRP(block), size, FREE);
        PACK(FTRP(block), size, FREE);
    }

    /* case IV: F | T | F */
    else {
        size += (GET_SIZE(PREV_BLKP(block)) + GET_SIZE(NEXT_BLKP(block)));
        block = PREV_BLKP(block);
        PACK(HDRP(block), size, FREE);
        PACK(FTRP(block), size, FREE);
    }
    return block;
}

static footer_t* get_footer(block_t *block) {
    return FTRP(block);
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

    // block_t *prev = ;
    // block_t *next = ;

    if (CHK_ALN(block)) {
        printf("Error: payload for block at %p is not aligned\n", block);
    }

    if (GET_SIZE(HDRP(block)) != GET_SIZE(FTRP(block))) {
        printf("Error: header does not match footer\n");
    }

    if (!GET_ALLOC(block) && !GET_ALLOC(NEXT_BLKP(block)))
    {
        printf("Error: free blocks at %p, %p escaped coalescing\n", 
                block, NEXT_BLKP(block));
    }

    // if (prev < mem_heap_lo() || prev > mem_heap_hi())
    // {
    //     printf("Error: prevPointer")
    // }
}
