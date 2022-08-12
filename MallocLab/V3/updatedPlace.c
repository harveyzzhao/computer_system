/*
 * place - Place block of asize bytes at start of free block block
 *         and split if remainder would be at least minimum block size
 */
/* $begin mmplace */
static void place(block_t *block, size_t asize) {

    printf("Placing block: original block of size %d", block->block_size);

    uint32_t split_size = GET_SIZE(block) - asize;

    if (split_size < MIN_BLOCK_SIZE) {
        printf("placing block: WHOLE\n");
        PACK(HDRP(block), GET_SIZE(block), ALLOC);
        PACK(FTRP(block), GET_SIZE(block), ALLOC);
        removeBlock(block);
    } 

    // else if (asize >= 128) {}
    else {
        printf("placing block OF SIZE %lu: SPLIT\n", asize);
        removeBlock(block);


        footer_t *splitBlock_footer = (void *)(FTRP(block));
        splitBlock_footer->block_size = asize;
        splitBlock_footer->allocated = ALLOC;

        block_t *splitBlock = (void *)splitBlock_footer - asize + sizeof(footer_t);
        splitBlock->block_size = asize;
        splitBlock->allocated = ALLOC;
        // PACK(HDRP(block), asize, ALLOC);    /* split the block by updating the header and marking it allocated*/
        // PACK(FTRP(block), asize, ALLOC);    /* set footer of allocated block*/

        block->block_size = split_size;
        block->allocated = FREE;
        footer_t *m_footer = get_footer(block);
        m_footer->block_size = split_size;
        m_footer->allocated = FREE;

        // printf("Bouta insert the split block of size %d\n", split_size);
        insertBlock(block);
    }

    /* TODO: delete when finished developing */
    // mm_checkheap(0);
}
/* $end mmplace */
