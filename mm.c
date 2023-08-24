/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk PTR.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your information in the following struct.
 ********************************************************/
team_t team = {
    /* Your student ID */
    "20191616",
    /* Your full name*/
    "Kunhwa Lee",
    /* Your email address */
    "lkh0107@sogang.ac.kr",
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8 // align size
#define WSIZE 4     // word size
#define DSIZE 8     // double word size

/* chunksize */
#define CHUNKSIZE (1 << 12) 
#define SMALLCHUNKSIZE (1 << 6)
/* max min */
#define MAX(x, y) ((x) > (y) ? (x) : (y)) 
#define MIN(x, y) ((x) < (y) ? (x) : (y)) 

#define PACK(size, alloc) ((size) | (alloc)) 

#define PUT(p, val) (*(unsigned int *)(p) = (unsigned int)(val)) 

#define GET_SIZE(p) ((*(unsigned int *)(p)) & ~0x7) 
#define GET_ALLOC(p) ((*(unsigned int *)(p)) & 0x1) 

#define HEADER(bp) ((char *)(bp)-WSIZE)             
#define FOOTER(bp) ((char *)(bp) + GET_SIZE(HEADER(bp)) - DSIZE) 

#define NEXT_BLOCK(bp) ((char *)(bp) + GET_SIZE(HEADER(bp)))     
#define PREV_BLOCK(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE))) 

#define NEXT_FREE_PTR(ptr) ((char *)(ptr))     
#define NEXT_FREE_REFER(ptr) (*(char **)(ptr)) 

#define PREV_FREE_PTR(ptr) ((char *)(ptr) + WSIZE)
#define PREV_FREE_REFER(ptr) (*(char **)(PREV_FREE_PTR(ptr))) 

// mm_init set
static void init_free_list();
static void set_logue();
int mm_init(void);

void **free_lists;
void *logue;
#define LIST 20 

// free_list set
static void insert_free_block(void *ptr, size_t size);
static void delete_free_block(void *ptr);
static int which_index(size_t size);

static void *place(void *ptr, size_t asize);
static void *find_place(size_t newsize);
static void *coalesce(void *ptr);

// allocating set
static void *extend_heap(size_t size);
void *mm_malloc(size_t size);
void mm_free(void *ptr);
void *mm_realloc(void *ptr, size_t size);


static void init_free_list()
{
    // printf("init_free_list\n");
    int index = 0;
    free_lists = (void **)malloc(sizeof(void *) * LIST);
    for (index = 0; index < LIST; index++)
    {
        free_lists[index] = NULL;
    }
}

static void set_logue()
{
    // printf("set_logue\n");
    //   cannot allocated the heap
    if ((long)(logue = mem_sbrk(4 * WSIZE)) == -1)
        return;
    // padding
    PUT(logue, 0);
    // input the prologue header
    PUT(logue + 1 * WSIZE, PACK(DSIZE, 1));
    // prologue footer
    PUT(logue + 2 * WSIZE, PACK(DSIZE, 1));
    // epilogue header
    PUT(logue + 3 * WSIZE, PACK(0, 1));
}

int mm_init(void)
{
    // printf("mm_init\n");
    init_free_list();
    set_logue();
    if (extend_heap(SMALLCHUNKSIZE) == NULL)
    {
        return -1;
    }
    return 0;
}

static int which_index(size_t size)
{
    // printf("index_from_size\nsize : %d, ", size);
    int index = 0;
    while (size > 1)
    {
        size = size >> 1;
        index++;
        if (index >= LIST - 1)
        {
            break;
        }
    }
    return index;
}

static void insert_free_block(void *ptr, size_t size)
{
    // printf("insert node\n");
    int index = 0;
    void *cur;
    void *prev = NULL;

    index = which_index(size);
    cur = free_lists[index];
    //find a position
    while (cur != NULL && size > GET_SIZE(HEADER(cur)))
    {
        prev = cur;
        cur = NEXT_FREE_REFER(cur);
    }
    if (cur == NULL)
    {
        // empty
        if (prev == NULL)
        {
            PUT(NEXT_FREE_PTR(ptr), NULL);
            PUT(PREV_FREE_PTR(ptr), NULL);
            free_lists[index] = ptr;
        }
        // end of the list
        else
        {
            PUT(NEXT_FREE_PTR(ptr), NULL);
            PUT(PREV_FREE_PTR(ptr), prev);
            PUT(NEXT_FREE_PTR(prev), ptr);
        }
    }
    else
    {
        // beginning
        if (prev == NULL)
        {
            PUT(NEXT_FREE_PTR(ptr), cur);
            PUT(PREV_FREE_PTR(ptr), NULL);
            PUT(PREV_FREE_PTR(cur), ptr);
            free_lists[index] = ptr;
        }
        //beteween
        else
        {
            PUT(NEXT_FREE_PTR(ptr), cur);
            PUT(PREV_FREE_PTR(cur), ptr);

            PUT(NEXT_FREE_PTR(prev), ptr);
            PUT(PREV_FREE_PTR(ptr), prev);
        }
    }
    return;
}

static void delete_free_block(void *ptr)
{
    // // printf("delete node\n");
    int index = 0;
    int size = GET_SIZE(HEADER(ptr));
    index = which_index(size);
    if (NEXT_FREE_REFER(ptr) != NULL)
    {
        // between
        if (PREV_FREE_REFER(ptr) != NULL)
        {
            PUT(PREV_FREE_PTR(NEXT_FREE_REFER(ptr)), PREV_FREE_REFER(ptr));
            PUT(NEXT_FREE_PTR(PREV_FREE_REFER(ptr)), NEXT_FREE_REFER(ptr));
        }
        // beginning
        else
        {
            PUT(PREV_FREE_PTR(NEXT_FREE_REFER(ptr)), NULL);
            free_lists[index] = NEXT_FREE_REFER(ptr);
        }
    }
    else
    {
        // end
        if (PREV_FREE_REFER(ptr) != NULL)
        {
            PUT(NEXT_FREE_PTR(PREV_FREE_REFER(ptr)), NULL);
        }
        // alone
        else
        {
            free_lists[index] = NULL;
        }
    }
    return;
}

static void *coalesce(void *ptr)
{
    // printf("coalesce\n");
    size_t prev_all = GET_ALLOC(HEADER(PREV_BLOCK(ptr)));
    size_t next_all = GET_ALLOC(HEADER(NEXT_BLOCK(ptr)));
    size_t size = GET_SIZE(HEADER(ptr));

    if (prev_all == 1 && next_all == 1)
    {
        return ptr;
    }
    else if (prev_all == 1 && next_all == 0)
    {
        delete_free_block(ptr);
        delete_free_block(NEXT_BLOCK(ptr));
        size += GET_SIZE(HEADER(NEXT_BLOCK(ptr)));
        PUT(HEADER(ptr), PACK(size, 0));
        PUT(FOOTER(ptr), PACK(size, 0));
    }
    else if (prev_all == 0 && next_all == 1)
    {
        delete_free_block(ptr);
        delete_free_block(PREV_BLOCK(ptr));
        size += GET_SIZE(HEADER(PREV_BLOCK(ptr)));
        ptr = PREV_BLOCK(ptr);
        PUT(HEADER(ptr), PACK(size, 0));
        PUT(FOOTER(ptr), PACK(size, 0));
    }
    else
    {
        delete_free_block(ptr);
        delete_free_block(PREV_BLOCK(ptr));
        delete_free_block(NEXT_BLOCK(ptr));
        size += GET_SIZE(HEADER(PREV_BLOCK(ptr))) + GET_SIZE(HEADER(NEXT_BLOCK(ptr)));
        ptr = PREV_BLOCK(ptr);
        PUT(HEADER(ptr), PACK(size, 0));
        PUT(FOOTER(ptr), PACK(size, 0));
    }
    insert_free_block(ptr, size);
    return ptr;
}

static void *place(void *ptr, size_t asize)
{
    // printf("place\n");
    size_t size = GET_SIZE(HEADER(ptr));
    size_t free_size = size - asize;

    delete_free_block(ptr);

    if (free_size <= DSIZE * 2)
    {
        PUT(HEADER(ptr), PACK(size, 1));
        PUT(FOOTER(ptr), PACK(size, 1));
    }
    // small one into the front
    else if (asize > free_size)
    {
        PUT(HEADER(ptr), PACK(free_size, 0));
        PUT(FOOTER(ptr), PACK(free_size, 0));

        PUT(HEADER(NEXT_BLOCK(ptr)), PACK(asize, 1));
        PUT(FOOTER(NEXT_BLOCK(ptr)), PACK(asize, 1));
        insert_free_block(ptr, free_size);
        return NEXT_BLOCK(ptr);
    }
    else
    {
        PUT(HEADER(ptr), PACK(asize, 1));
        PUT(FOOTER(ptr), PACK(asize, 1));
        PUT(HEADER(NEXT_BLOCK(ptr)), PACK(free_size, 0));
        PUT(FOOTER(NEXT_BLOCK(ptr)), PACK(free_size, 0));
        insert_free_block(NEXT_BLOCK(ptr), free_size);
    }
    return ptr;
}

static void *find_place(size_t asize)
{
    void *p;
    for (int index = which_index(asize); index < LIST; index++)
    {
        if (index == LIST - 1 || free_lists[index])
        {
            p = free_lists[index];
            while (p != NULL && ((asize > GET_SIZE(HEADER(p)))))
            {
                p = NEXT_FREE_REFER(p);
            }
            if (p != NULL)
                break;
        }
    }
    return p;
}

static void *extend_heap(size_t size)
{
    // printf("extend heap\n");
    void *ptr;
    if ((ptr = mem_sbrk(size)) == (void *)-1)
        return NULL;
    // header
    PUT(HEADER(ptr), PACK(size, 0));
    // footer
    PUT(FOOTER(ptr), PACK(size, 0));
    // epilogue
    PUT(HEADER(NEXT_BLOCK(ptr)), PACK(0, 1));
    // insert_free_block
    insert_free_block(ptr, size);
    return coalesce(ptr);
}

void mm_free(void *ptr)
{
    // printf("mm_free\n");
    size_t size = GET_SIZE(HEADER(ptr));
    PUT(HEADER(ptr), PACK(size, 0));
    PUT(FOOTER(ptr), PACK(size, 0));
    insert_free_block(ptr, size);
    coalesce(ptr);
}

void *mm_malloc(size_t size)
{
    // printf("mm_malloc\n");
    if (size == 0)
        return NULL;

    size_t asize;  // adjust size
    size_t extend; // extend heap if neccessary
    void *p;
    // align block size
    if (size <= DSIZE)     // line:vm:mm:sizeadjust1
        asize = 2 * DSIZE; // line:vm:mm:sizeadjust2
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    p = find_place(asize);
    // printf("find_place\n");
    if (p == NULL)
    {
        extend = MAX(asize, CHUNKSIZE);
        // cannot extend the heap
        p = extend_heap(extend);
        if (p == (void *)-1)
            return NULL;
    }
    p = place(p, asize);
    return p;
}

void *mm_realloc(void *ptr, size_t size)
{ // printf("mm_realloc\n");
    if (size == 0)
        return NULL;

    void *newptr;
    size_t asize = size;

    newptr = ptr;
    // align block size
    if (asize <= DSIZE)    // line:vm:mm:sizeadjust1
        asize = 2 * DSIZE; // line:vm:mm:sizeadjust2
    else
        asize = DSIZE * ((asize + (DSIZE) + (DSIZE - 1)) / DSIZE);

    // no space
    if (GET_SIZE(HEADER(ptr)) < asize)
    {
        // extendable
        if (!GET_ALLOC(HEADER(NEXT_BLOCK(ptr))) || !GET_SIZE(HEADER(NEXT_BLOCK(ptr))))
        {
            int size_sum = GET_SIZE(HEADER(ptr)) + GET_SIZE(HEADER(NEXT_BLOCK(ptr)));
            //but still no space
            if (size_sum < asize)
            {
                newptr = mm_malloc(asize);
                memcpy(newptr, ptr, MIN(size, asize));
                mm_free(ptr);
            }
            //yes space
            else
            {
                delete_free_block(NEXT_BLOCK(ptr));
                PUT(HEADER(ptr), PACK(size_sum, 1));
                PUT(FOOTER(ptr), PACK(size_sum, 1));
            }
        }
        // not extendable
        else
        {
            newptr = mm_malloc(asize);
            memcpy(newptr, ptr, MIN(size, asize));
            mm_free(ptr);
        }
    }

    return newptr;
}
