/**
 * @file mm.c
 * @brief A 64-bit struct-based implicit free list memory allocator
 *
 * 15-213: Introduction to Computer Systems
 *
 * TODO: Dynamic Storage Allocator using segmented list, first fit, and LIFO
 *
 *************************************************************************
 *
 *
 * @author Jason Hoang <jvhoang@andrew.cmu.edu>
 */

#include <assert.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"
#include "mm.h"

/* Do not change the following! */

#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#define memset mem_memset
#define memcpy mem_memcpy
#endif /* def DRIVER */

/* You can change anything from here onward */

/*
 *****************************************************************************
 * If DEBUG is defined (such as when running mdriver-dbg), these macros      *
 * are enabled. You can use them to print debugging output and to check      *
 * contracts only in debug mode.                                             *
 *                                                                           *
 * Only debugging macros with names beginning "dbg_" are allowed.            *
 * You may not define any other macros having arguments.                     *
 *****************************************************************************
 */
#ifdef DEBUG
/* When DEBUG is defined, these form aliases to useful functions */
#define dbg_printf(...) printf(__VA_ARGS__)
#define dbg_requires(expr) assert(expr)
#define dbg_assert(expr) assert(expr)
#define dbg_ensures(expr) assert(expr)
#define dbg_printheap(...) print_heap(__VA_ARGS__)
#else
/* When DEBUG is not defined, no code gets generated for these */
/* The sizeof() hack is used to avoid "unused variable" warnings */
#define dbg_printf(...) (sizeof(__VA_ARGS__), -1)
#define dbg_requires(expr) (sizeof(expr), 1)
#define dbg_assert(expr) (sizeof(expr), 1)
#define dbg_ensures(expr) (sizeof(expr), 1)
#define dbg_printheap(...) ((void)sizeof(__VA_ARGS__))
#endif

/* Basic constants */

typedef uint64_t word_t;

/** @brief Word and header size (bytes) */
static const size_t wsize = sizeof(word_t);

/** @brief Double word size (bytes) */
static const size_t dsize = 2 * wsize;

/** @brief Minimum block size (bytes) */
static const size_t min_block_size = dsize;

/**
 * TODO: Amount heap will be extended by
 * (Must be divisible by dsize)
 */
static const size_t chunksize = (1 << 12);

/**
 * TODO: mask to get allocated bit from header
 */
static const word_t alloc_mask = 0x1;

/**
 * TODO: mask to get payload size from header
 */
static const word_t size_mask = ~(word_t)0xF;

static const size_t numSegs = 15;

/** @brief Represents the header and payload of one block in the heap */
typedef struct block {
    /** @brief Header contains size + allocation flag */
    word_t header;

    /**
     * @brief A pointer to the block payload.
     */
    union { // Union such that it is a payload if allocated and pointer
            // otherwise
        struct {
            struct block *next;
            struct block *prev;
        };
        char payload[0];
    };

} block_t;

/* Global variables */

/** @brief Pointer to first block in the heap */
static block_t *heap_start = NULL;

// Points to segment list
static block_t *segList[numSegs];

/*
 *****************************************************************************
 * The functions below are short wrapper functions to perform                *
 * bit manipulation, pointer arithmetic, and other helper operations.        *
 *                                                                           *
 * We've given you the function header comments for the functions below      *
 * to help you understand how this baseline code works.                      *
 *                                                                           *
 * Note that these function header comments are short since the functions    *
 * they are describing are short as well; you will need to provide           *
 * adequate details for the functions that you write yourself!               *
 *****************************************************************************
 */

/*
 * ---------------------------------------------------------------------------
 *                        BEGIN SHORT HELPER FUNCTIONS
 * ---------------------------------------------------------------------------
 */

/**
 * @brief Returns the maximum of two integers.
 * @param[in] x
 * @param[in] y
 * @return `x` if `x > y`, and `y` otherwise.
 */
static size_t max(size_t x, size_t y) {
    return (x > y) ? x : y;
}

/**
 * @brief Rounds `size` up to next multiple of n
 * @param[in] size
 * @param[in] n
 * @return The size after rounding up
 */
static size_t round_up(size_t size, size_t n) {
    return n * ((size + (n - 1)) / n);
}

/**
 * @brief Packs the `size` and `alloc` and 'prevalloc" of a block into a word
 * suitable for use as a packed value.
 *
 * Packed values are used for both headers and footers.
 *
 * The allocation status is packed into the lowest bit of the word.
 *
 * @param[in] size The size of the block being represented
 * @param[in] alloc True if the block is allocated
 * @param[in] isPrevAlloc True is the previous block is allocated
 * @return The packed value
 */
static word_t pack(size_t size, bool alloc, bool isPrevAlloc,
                   bool isPrevMiniBlock) {
    word_t word = size;
    if (alloc) {
        word |= alloc_mask;
    }
    if (isPrevAlloc) {
        word |= 0x2;
    }
    if (isPrevMiniBlock) {
        word |= 0x4;
    }
    return word;
}

/**
 * @brief Extracts the size represented in a packed word.
 *
 * This function simply clears the lowest 4 bits of the word, as the heap
 * is 16-byte aligned.
 *
 * @param[in] word
 * @return The size of the block represented by the word
 */
static size_t extract_size(word_t word) {
    return (word & size_mask);
}

/**
 * @brief Extracts the size of a block from its header.
 * @param[in] block
 * @return The size of the block
 */
static size_t get_size(block_t *block) {
    return extract_size(block->header);
}

/**
 * @brief Given a payload pointer, returns a pointer to the corresponding
 *        block.
 * @param[in] bp A pointer to a block's payload
 * @return The corresponding block
 */
static block_t *payload_to_header(void *bp) {
    return (block_t *)((char *)bp - offsetof(block_t, payload));
}

/**
 * @brief Given a block pointer, returns a pointer to the corresponding
 *        payload.
 * @param[in] block
 * @return A pointer to the block's payload
 * @pre The block must be a valid block, not a boundary tag.
 */
static void *header_to_payload(block_t *block) {
    dbg_requires(get_size(block) != 0);
    return (void *)(block->payload);
}

/**
 * @brief Given a block pointer, returns a pointer to the corresponding
 *        footer.
 * @param[in] block
 * @return A pointer to the block's footer
 * @pre The block must be a valid block, not a boundary tag.
 */
static word_t *header_to_footer(block_t *block) {
    dbg_requires(get_size(block) != 0 &&
                 "Called header_to_footer on the epilogue block");
    return (word_t *)(block->payload + get_size(block) - dsize);
}

/**
 * @brief Given a block footer, returns a pointer to the corresponding
 *        header.
 * @param[in] footer A pointer to the block's footer
 * @return A pointer to the start of the block
 * @pre The footer must be the footer of a valid block, not a boundary tag.
 */
static block_t *footer_to_header(word_t *footer) {
    size_t size = extract_size(*footer);
    dbg_assert(size != 0 && "Called footer_to_header on the prologue block");
    return (block_t *)((char *)footer + wsize - size);
}

/**
 * @brief Returns the payload size of a given block.
 *
 * The payload size is equal to the entire block size minus the sizes of the
 * block's header and footer.
 *
 * @param[in] block
 * @return The size of the block's payload
 */
static size_t get_payload_size(block_t *block) {
    size_t asize = get_size(block);
    return asize - wsize;
}

/**
 * @brief Returns the allocation status of a given header value.
 *
 * This is based on the lowest bit of the header value.
 *
 * @param[in] word
 * @return The allocation status correpsonding to the word
 */
static bool extract_alloc(word_t word) {
    return (bool)(word & alloc_mask);
}
/**
 * @brief Returns the allocation status of a previous header
 *
 * This is based on the second lowest bit of the header value.
 *
 * @param[in] block
 * @return The allocation status correpsonding to the word
 */
static bool getPrevAlloc(block_t *block) {
    return (bool)((block->header & 0x2) >> 1);
}
/**
 * @brief Returns the allocation status of previous mini block
 *
 *
 * @param[in] block
 * @return The allocation status correpsonding to the word
 */
static bool getPrevMiniBlock(block_t *block) {
    return (bool)((block->header & 0x4) >> 2);
}
/**
 * @brief Returns the allocation status of a block, based on its header.
 * @param[in] block
 * @return The allocation status of the block
 */
static bool get_alloc(block_t *block) {
    return extract_alloc(block->header);
}

/**
 * @brief Writes an epilogue header at the given address.
 *
 * The epilogue header has size 0, and is marked as allocated.
 *
 * @param[out] block The location to write the epilogue header
 * @param[in] isPrevAlloc The allocation status of the previous block
 */
static void write_epilogue(block_t *block, bool isPrev, bool isPrevMiniBlock) {
    dbg_requires(block != NULL);
    dbg_requires((char *)block == mem_heap_hi() - 7);
    block->header = pack(0, true, isPrev, isPrevMiniBlock);
}

/**
 * @brief Writes a block starting at the given address.
 *
 * This function writes both a header and footer, where the location of the
 * footer is computed in relation to the header.
 *
 * TODO: Are there any preconditions or postconditions?
 *
 * @param[out] block The location to begin writing the block header
 * @param[in] size The size of the new block
 * @param[in] currAlloc The allocation status of the new block
 */
static void write_block(block_t *block, size_t size, bool currAlloc) {
    dbg_requires(block != NULL);
    dbg_requires(size > 0);
    bool isPrevAlloc = getPrevAlloc(block);
    bool isPrevMiniBlock = getPrevMiniBlock(block);
    block->header = pack(size, currAlloc, isPrevAlloc, isPrevMiniBlock);
    if (currAlloc == false) {
        if (size > min_block_size) {
            word_t *footer = header_to_footer(block);
            *footer = pack(size, currAlloc, isPrevAlloc, isPrevMiniBlock);
        }
    }
}

/**
 * @brief Finds the next consecutive block on the heap.
 *
 * This function accesses the next block in the "implicit list" of the heap
 * by adding the size of the block.
 *
 * @param[in] block A block in the heap
 * @return The next consecutive block on the heap
 * @pre The block is not the epilogue
 */
static block_t *find_next(block_t *block) {
    dbg_requires(block != NULL);
    dbg_requires(get_size(block) != 0 &&
                 "Called find_next on the last block in the heap");
    return (block_t *)((char *)block + get_size(block));
}

/**
 * @brief Finds the footer of the previous block on the heap.
 * @param[in] block A block in the heap
 * @return The location of the previous block's footer
 */
static word_t *find_prev_footer(block_t *block) {
    // Compute previous footer position as one word before the header
    return &(block->header) - 1;
}

/**
 * @brief Finds the previous consecutive block on the heap.
 *
 * This is the previous block in the "implicit list" of the heap.
 *
 * If the function is called on the first block in the heap, NULL will be
 * returned, since the first block in the heap has no previous block!
 *
 * The position of the previous block is found by reading the previous
 * block's footer to determine its size, then calculating the start of the
 * previous block based on its size.
 *
 * @param[in] block A block in the heap
 * @return The previous consecutive block in the heap.
 */
static block_t *find_prev(block_t *block) {
    dbg_requires(block != NULL);
    word_t *footerp = find_prev_footer(block);

    // Return NULL if called on first block in the heap
    if (extract_size(*footerp) == 0) {
        return NULL;
    }

    return footer_to_header(footerp);
}

/*
 * ---------------------------------------------------------------------------
 *                        END SHORT HELPER FUNCTIONS
 * ---------------------------------------------------------------------------
 */

/******** The remaining content below are helper and debug routines ********/
/**
 * @brief determines the index the block should be inserted based on the given
 * size
 *
 * @param[in] intended added block size
 * return the index in the segList the block will go
 */
static size_t findIndex(size_t size) {
    if (size <= min_block_size) {
        return 0;
    }
    for (size_t i = 0; i < numSegs - 1; i++) {
        size_t target = min_block_size << (i + 1);
        if (size < target) {
            return i;
        }
    }
    return numSegs - 1;
}
/**
 * @brief sets prev next to block next
 *
 * @param[in] block block to be reached
 * @param[in] temp counter block to increment
 * @param[in] prev counter that trails temp
 */
static void shiftHelper(block_t *block, block_t *temp, block_t *prev) {
    while (temp != block) {
        prev = temp;
        temp = temp->next;
    }
    prev->next = temp->next;
}
/**
 * @brief removed a block from the segList at the given index
 *
 * @param[in] block the block being removed
 * @param[in] index the index of the block parameter
 *
 */
static void removeFromFree(block_t *block, size_t index) {
    block_t *prev = block->prev;
    block_t *next = block->next;
    if (block != NULL) {
        if (index != 0) {
            if (prev != NULL) {
                // case 1
                prev->next = next;
                // case 2
                if (next != NULL) {
                    next->prev = prev;
                }
            } else {
                // case 3
                segList[index] = next;
                // case 4
                if (next != NULL) {

                    segList[index]->prev = NULL;
                }
            }
        } else {
            if (block != segList[0]) {
                block_t *temp = segList[0]->next;
                block_t *prev = segList[0];
                shiftHelper(block, temp, prev);
                return;
            }
            segList[0] = segList[0]->next;
        }
    }
}

/**
 * @brief adds a block at the given index to the segList
 *
 * @param[in] block the block to be added
 * @param[in] index the index in which it will be put
 */
static void addToFree(block_t *block, size_t index) {
    if (block == NULL) {
        return;
    }
    block_t *addBlock = segList[index];
    if (index != 0) {
        block->prev = NULL;
        block->next = addBlock;
        if (addBlock != NULL) {
            segList[index]->prev = block;
        }
        segList[index] = block;
    } else {
        segList[index] = block;
        segList[index]->next = addBlock;
    }
}

/**
 * @brief coalesces free adjacent blocks
 *
 * @param[in] block to be coalesced at
 */
static block_t *coalesce_block(block_t *block) {
    block_t *prev;
    block_t *next = find_next(block);
    bool isPrevAlloc = getPrevAlloc(block);
    bool isNextAlloc = get_alloc(next);
    if (!isPrevAlloc) {
        prev = find_prev(block);
    }
    size_t blockSize = get_size(block);
    size_t removed;
    size_t toBeAdded;
    if (isPrevAlloc) {
        removed = get_size(next);
        // case 1
        if (isNextAlloc) {
            write_block(block, blockSize, false);
            write_block(next, get_size(next), true);
        } else { // case 2
            toBeAdded = removed + blockSize;
            removeFromFree(next, findIndex(get_size(next)));
            write_block(block, toBeAdded, false);
            write_block(next, toBeAdded, true);
        }
    } else {
        removed = get_size(prev);
        // case 3
        if (isNextAlloc) {
            toBeAdded = removed + blockSize;
        } else { // case 4
            removed += get_size(next);
            toBeAdded = removed + blockSize;
            removeFromFree(next, findIndex(get_size(next)));
        }
        removeFromFree(prev, findIndex(get_size(prev)));
        block = prev;
        write_block(block, toBeAdded, false);
        write_block(next, get_size(next), false);
    }
    return block;
}

/**
 * @brief extends length of the heap
 *
 *
 * @param[in] size
 * @return
 */
static block_t *extend_heap(size_t size) {
    void *bp;

    // Allocate an even number of words to maintain alignment
    size = round_up(size, dsize);
    if ((bp = mem_sbrk(size)) == (void *)-1) {
        return NULL;
    }
    // Initialize free block header/footer
    block_t *block = payload_to_header(bp);
    write_block(block, size, false);

    // Create new epilogue header
    block_t *block_next = find_next(block);
    write_epilogue(block_next, false, false);

    // Coalesce in case the previous block was free
    block = coalesce_block(block);

    return block;
}

/**
 * @brief splits a block into an allocated and free section
 *
 *
 * @param[in] block
 * @param[in] asize
 * @pre asize>0
 */
static void split_block(block_t *block, size_t asize) {
    dbg_requires(get_alloc(block));
    size_t size = get_size(block);
    if ((size - asize) >= min_block_size) {
        // bool isPrevAlloc = getPrevAlloc(block);
        write_block(block, asize, true);

        block_t *next = find_next(block);
        next->header = next->header | 0x2;
        write_block(next, size - asize, false);
        addToFree(next, findIndex(get_size(next)));
        next = find_next(next);
        write_block(next, get_size(next), get_alloc(next));
    }

    dbg_ensures(get_alloc(block));
}

/**
 * @brief first fit to find a block of the necessary minimum size
 *
 *
 * @param[in] asize
 * @return
 */
static block_t *find_fit(size_t asize) {
    size_t count = 5;
    block_t *fit_block = NULL;
    size_t min_fit_size = 0;
    size_t size = findIndex(asize);
    for (size_t i = size; i < numSegs; i++) {
        for (block_t *block = segList[i]; (block != NULL && count > 0);
             block = block->next) {
            if (asize <= get_size(block)) {
                if (count == 5) {
                    fit_block = block;
                    min_fit_size = get_size(fit_block);
                }
                if (get_size(block) < min_fit_size) {
                    fit_block = block;
                    min_fit_size = get_size(fit_block);
                }
                count = count - 1;
            }
        }
        if (fit_block != NULL) {
            return fit_block;
        }
    }

    return NULL; // no fit found
}
static bool checkAlignment(block_t *currBlock, int n) {
    return (uintptr_t)currBlock % 16 == n;
}

/**
 * @brief scans the heap and checks it for possible errors
 *
 *
 * @param[in] line
 * @return
 */

bool mm_checkheap(int line) {
    // check if heap exists
    if (heap_start == NULL) {
        printf("1: Line %d\n", line);
        return false;
    }
    int numFreeHeap = 0;
    int numFreeSegList = 0;
    // check for prologue
    void *firstHeapByte = mem_heap_lo();
    block_t *prologue = (block_t *)(char *)(firstHeapByte);
    bool pAllocTrue = get_alloc(prologue);
    size_t prologueSize = get_size(prologue);
    // prologue validity check

    if (prologueSize > 0 || pAllocTrue == false) {
        printf("2: Line %d\n", line);
        return false;
    }
    // alignment
    if (!checkAlignment(prologue, 0)) {
        printf("3: Line %d\n", line);
        return false;
    }

    // check for epilogue
    void *lastHeapByte = mem_heap_hi();
    char *charLastHeapByte = (char *)lastHeapByte;
    block_t *epilogue = (block_t *)(charLastHeapByte - wsize + 1);
    bool eAllocTrue = get_alloc(epilogue);
    size_t epilogueSize = get_size(epilogue);
    // epilogue validity check
    if (epilogueSize > 0 || eAllocTrue == false) {
        printf("4: Line %d\n", line);
        return false;
    }
    // alignment
    if (!checkAlignment(epilogue, 8)) {
        printf("5: Line %d\n", line);
        return false;
    }

    // iterate through heap
    for (block_t *currBlock = heap_start; currBlock != epilogue;
         currBlock = find_next(currBlock)) {
        if (get_alloc(currBlock) == false) {
            numFreeHeap++;
        }
        // each block address alignment
        if (!checkAlignment(currBlock, 8)) {
            printf("6: Line %d\n", line);
            return false;
        }
        // heap boundaries
        if (currBlock < heap_start || currBlock > epilogue) {
            printf("7: Line %d\n", line);
            return false;
        }
        // header and footer match
        if (currBlock->header != *header_to_footer(currBlock)) {
            printf("8: Line %d\n", line);
            return false;
        }
        // no two free blocks in a row
        if (!get_alloc(currBlock)) {
            if (!get_alloc(find_next(currBlock))) {
                printf("9: Line %d\n", line);
                return false;
            }
            if (find_prev(currBlock) != NULL) {
                if (get_alloc(find_prev(currBlock))) {
                    printf("10: Line %d\n", line);
                    return false;
                }
            }
        }
        // pointer consistency
        bool goodPointer = true;
        if (!get_alloc(currBlock)) {
            if (currBlock->next != NULL) {
                goodPointer = (currBlock->next->prev == currBlock);
            }
        }
        if (goodPointer == false) {
            printf("11: Line %d\n", line);
            return false;
        }
    }

    // iterate through segment list
    for (size_t i = 0; i < numSegs; i++) {
        block_t *currBlock = segList[i];
        // heap boundaries
        if (currBlock < heap_start || currBlock > epilogue) {
            printf("13: Line %d\n", line);
            return false;
        }
        // pointer consistency
        bool goodPointerSeg = true;
        if (!get_alloc(currBlock)) {
            if (currBlock->next != NULL) {
                goodPointerSeg = (currBlock->next->prev == currBlock);
            }
        }
        if (goodPointerSeg == false) {
            printf("14: Line %d\n", line);
            return false;
        }
        if (!get_alloc(currBlock)) {
            numFreeSegList++;
        }
    }

    // Match free in both lists
    if (numFreeSegList != numFreeHeap) {
        printf("15: Line %d\n", line);
        return false;
    }
    return true;
}

/**
 * @brief initializes heap and segList
 *
 *
 * @return
 */
bool mm_init(void) {
    // Create the initial empty heap
    word_t *start = (word_t *)(mem_sbrk(2 * wsize));

    if (start == (void *)-1) {
        return false;
    }

    start[0] = pack(0, true, false, false); // Heap prologue (block footer)
    start[1] = pack(0, true, true, false);  // Heap epilogue (block header)

    // Heap starts with first "block header", currently the epilogue
    heap_start = (block_t *)&(start[1]);

    for (size_t i = 0; i < numSegs; i++) {
        segList[i] = NULL;
    }

    // Extend the empty heap with a free block of chunksize bytes
    block_t *temp = extend_heap(chunksize);
    if (temp == NULL) {
        return false;
    }
    addToFree(temp, findIndex(get_size(temp)));
    block_t *next = find_next(temp);
    write_block(next, get_size(next), get_alloc(next));

    return true;
}

/**
 * @brief creates a space in memory of the given size
 *
 *
 * @param[in] size
 * @return
 */
void *malloc(size_t size) {
    dbg_requires(mm_checkheap(__LINE__));

    size_t asize;      // Adjusted block size
    size_t extendSize; // Amount to extend heap if no fit is found
    block_t *currBlock;
    void *bp = NULL;

    // Initialize heap if it isn't initialized
    if (heap_start == NULL) {
        mm_init();
    }

    // Ignore spurious request
    if (size == 0) {
        dbg_ensures(mm_checkheap(__LINE__));
        return bp;
    }

    // Adjust block size to include overhead and to meet alignment requirements
    asize = max(round_up(size + wsize, dsize), min_block_size);

    // Search the free list for a fit
    currBlock = find_fit(asize);

    // If no fit is found, request more memory, and then and place the block
    if (currBlock == NULL) {
        // Always request at least chunksize
        extendSize = max(asize, chunksize);
        block_t *temp = extend_heap(extendSize);
        // extend_heap returns an error
        if (temp == NULL) {
            return bp;
        } else {
            currBlock = temp;
        }
    } else {
        removeFromFree(currBlock, findIndex(get_size(currBlock)));
    }

    // The block should be marked as free
    dbg_assert(!get_alloc(currBlock));

    // Mark block as allocated
    size_t currBlockSize = get_size(currBlock);
    write_block(currBlock, currBlockSize, true);
    block_t *next = find_next(currBlock);
    next->header = next->header | 0x2;
    write_block(next, get_size(next), get_alloc(next));

    // Try to split the block if too large
    split_block(currBlock, asize);

    bp = header_to_payload(currBlock);

    dbg_ensures(mm_checkheap(__LINE__));

    return bp;
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] bp
 */
void free(void *bp) {
    dbg_requires(mm_checkheap(__LINE__));

    if (bp == NULL) {
        return;
    }

    block_t *block = payload_to_header(bp);
    size_t size = get_size(block);

    // The block should be marked as allocated
    dbg_assert(get_alloc(block));

    // Mark the block as free
    write_block(block, size, false);

    // Try to coalesce the block with its neighbors
    block = coalesce_block(block);

    // add it to the free segList
    addToFree(block, findIndex(get_size(block)));

    dbg_ensures(mm_checkheap(__LINE__));
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] ptr
 * @param[in] size
 * @return
 */
void *realloc(void *ptr, size_t size) {
    block_t *block = payload_to_header(ptr);
    size_t copysize;
    void *newptr;

    // If size == 0, then free block and return NULL
    if (size == 0) {
        free(ptr);
        return NULL;
    }

    // If ptr is NULL, then equivalent to malloc
    if (ptr == NULL) {
        return malloc(size);
    }

    // Otherwise, proceed with reallocation
    newptr = malloc(size);

    // If malloc fails, the original block is left untouched
    if (newptr == NULL) {
        return NULL;
    }

    // Copy the old data
    copysize = get_payload_size(block); // gets size of old payload
    if (size < copysize) {
        copysize = size;
    }
    memcpy(newptr, ptr, copysize);

    // Free the old block
    free(ptr);
    return newptr;
}

/**
 * @brief
 *
 * <What does this function do?>
 * <What are the function's arguments?>
 * <What is the function's return value?>
 * <Are there any preconditions or postconditions?>
 *
 * @param[in] elements
 * @param[in] size
 * @return
 */
void *calloc(size_t elements, size_t size) {
    void *bp;
    size_t asize = elements * size;

    if (elements == 0) {
        return NULL;
    }
    if (asize / elements != size) {
        // Multiplication overflowed
        return NULL;
    }

    bp = malloc(asize);
    if (bp == NULL) {
        return NULL;
    }

    // Initialize all bits to 0
    memset(bp, 0, asize);

    return bp;
}

/*
 *****************************************************************************
 * Do not delete the following super-secret(tm) lines!                       *
 *                                                                           *
 * 53 6f 20 79 6f 75 27 72 65 20 74 72 79 69 6e 67 20 74 6f 20               *
 *                                                                           *
 * 66 69 67 75 72 65 20 6f 75 74 20 77 68 61 74 20 74 68 65 20               *
 * 68 65 78 61 64 65 63 69 6d 61 6c 20 64 69 67 69 74 73 20 64               *
 * 6f 2e 2e 2e 20 68 61 68 61 68 61 21 20 41 53 43 49 49 20 69               *
 *                                                                           *
 * 73 6e 27 74 20 74 68 65 20 72 69 67 68 74 20 65 6e 63 6f 64               *
 * 69 6e 67 21 20 4e 69 63 65 20 74 72 79 2c 20 74 68 6f 75 67               *
 * 68 21 20 2d 44 72 2e 20 45 76 69 6c 0a c5 7c fc 80 6e 57 0a               *
 *                                                                           *
 *****************************************************************************
 */