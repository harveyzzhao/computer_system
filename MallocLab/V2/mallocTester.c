#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

typedef struct {
    uint32_t allocated : 1;
    uint32_t block_size : 31;
    // uint32_t _;
    union {
        struct {
            struct block_t* next;
            struct block_t* prev;
        };
        int payload[0]; 
    } body; //What's the alignment requirement and memory requirement of body
} block_t;

static block_t *m_root = NULL;    /* root of the explicit free list */
static block_t *m_tail = NULL;    /* tail of the explicit free list */

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
        block->body.prev = NULL;
        m_root = (void *)block;
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
        m_root = NULL;  //FIXME: hey! You are setting the address to NULL
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

    printf("ROOT: %d | %s\n", m_root->block_size, (m_root->allocated) ? "ALLOC" : "FREE");
    
    /* check middle */
    while ((void *)block != m_tail)
    {
        prv = (void *)(block->body.prev);
        nxt = (void *)(block->body.next);
        printf("%d | %s\n", block->block_size, (block->allocated) ? "ALLOC" : "FREE");

        block = (void *)nxt;
    }

    nxt = (void *)(block->body.next);
    if ((void *)nxt != NULL)
    {
        printf("Error: tail has non-NULL NEXTptr\n");
    }
    printf("%d | %s\n", block->block_size, (block->allocated) ? "ALLOC" : "FREE");
    printf("TAIL: %d | %s\n", m_tail->block_size, (m_tail->allocated) ? "ALLOC" : "FREE");
}

int main() {
    block_t* first;
    first = (block_t *) malloc(sizeof(block_t));
    
    // first->body.next = NULL;
    // first->body.prev = NULL;
    first->allocated = 0;
    first->block_size = 1;
    insertBlock(first);


    block_t* m_branch;
    m_branch = (block_t *) malloc(sizeof(block_t));
    
    m_branch->allocated = 0;
    m_branch->block_size = 2;
    // m_branch->body.next = NULL;
    // m_branch->body.prev = (void *)first;
    // first->body.next = (void *)m_branch;

    // printf("%p\n", m_branch);
    // printf("%d\n", m_branch->allocated);

    // block_t *temp = (void *)(first->body.next);    //assign th
    // temp->body.next = NULL;
    // printf("%d\n", temp->block_size);
    // printf("%p\n",(m_branch->body.prev->allocated);
    insertBlock(m_branch);
    
    // printf("%d\n", m_root->block_size);
    // printf("%d\n", m_tail->block_size);

    block_t* second;
    second = (block_t *) malloc(sizeof(block_t));
    
    second->allocated = 0;
    second->block_size = 3;
    insertBlock(second);

    //test removeBlock
    removeBlock(second);
    removeBlock(first);

    checklist();
}