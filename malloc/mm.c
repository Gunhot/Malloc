/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
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
    "20181663",
    /* Your full name*/
    "kyunghee Lee",
    /* Your email address */
    "dlrudgml6@sogang.ac.kr",
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8
#define WSIZE	4
#define DSIZE	8
#define INITCHUNKSIZE (1<<6)
#define CHUNKSIZE	(1<<12)

#define LIST    20      
#define REALLOC_BUFFER  (1<<7)    

#define MAX(x,y) ((x) > (y)? (x) : (y))
#define MIN(x, y) ((x) < (y) ? (x) : (y))

#define PACK(size, alloc)	((size) | (alloc))

#define GET(p)	(*(unsigned int *)(p))
#define PUT(p, val)	(*(unsigned int *)(p) = (val))
#define PUT_NOTAG(p, val) (*(unsigned int *)(p) = (val))

#define SET_PTR(p, ptr) (*(unsigned int *)(p) = (unsigned int)(ptr))

#define GET_SIZE(p)	(GET(p) & ~0x7)
#define GET_ALLOC(p)	(GET(p) & 0x1)
#define GET_TAG(p)   (GET(p) & 0x2)
#define SET_RATAG(p)   (GET(p) |= 0x2)
#define REMOVE_RATAG(p) (GET(p) &= ~0x2)

#define HDRP(bp)	((char*)(bp) - WSIZE)
#define FTRP(bp)	((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define NEXT_BLK(bp)	((char *)(bp) + GET_SIZE(HDRP(bp)))
#define NEXT_BLKP(bp)	((char *)(bp) + GET_SIZE(((char *)(bp) -WSIZE)))
#define PREV_BLKP(bp)	((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))


#define PRED_PTR(ptr) ((char *)(ptr))
#define SUCC_PTR(ptr) ((char *)(ptr) + WSIZE)

#define PRED(ptr) (*(char **)(ptr))
#define SUCC(ptr) (*(char **)(SUCC_PTR(ptr)))

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

static char *mem_heap;
static char *mem_brk;
static char *mem_max_addr;
//void **free_lists;
void **free_lists;

static void *extend_heap(size_t size);
static void *coalesce(void *ptr);
static void *place(void *ptr, size_t asize);
static void insert_node(void *ptr, size_t size);
static void delete_node(void *ptr);

static void *extend_heap(size_t size)
{
    size_t tempsize=size;
    void * ptr= mem_sbrk(tempsize);

    //not enough space
    if(ptr == (void * ) -1)
        return NULL;

    //set header and footer infomation
    //header
    PUT_NOTAG(HDRP(ptr),PACK(tempsize,0));
    //footer
    PUT_NOTAG(FTRP(ptr),PACK(tempsize,0));
    PUT_NOTAG(HDRP(NEXT_BLKP(ptr)),PACK(0,1));
    //insert free node
    insert_node(ptr,tempsize);

    return coalesce(ptr);
}
//insert the node to the segregated free list
static void insert_node(void * ptr, size_t size)
{
    int index;
    void *next = ptr;
    void *before = NULL;

    for(index=0;index < LIST -1; index++ )
    {
        if(size > 1)
        {
            size = size >> 1;
        }
        else break;
    }
    next = free_lists[index];
    //traverse the free list to find a position to input the node
    while( next !=NULL && size < GET_SIZE(HDRP(next)))
    {
        before = next;
        next = PRED(next);
    }
    if(next != NULL)
    {
        //insert between the list
        if(before!= NULL)
        {
            SET_PTR(PRED_PTR(ptr),next);
            SET_PTR(SUCC_PTR(next), ptr);
            SET_PTR(PRED_PTR(before), ptr);
            SET_PTR(SUCC_PTR(ptr), before);
        }
        //insert at the begining of the list
        else
        {
            SET_PTR(PRED_PTR(ptr), next);
            SET_PTR(SUCC_PTR(next), ptr);
            SET_PTR(SUCC_PTR(ptr), NULL);
            //update the root of the free list
            free_lists[index]= ptr;
        }
    }
    //at the end of the list
    else
    {
        //at the end of the list
        if(before!=NULL)
        {
            SET_PTR(PRED_PTR(ptr),NULL);
            SET_PTR(SUCC_PTR(ptr), before);
            SET_PTR(PRED_PTR(before),ptr);
        }
        //the list is empty initially at that index
        else
        {
            SET_PTR(PRED_PTR(ptr),NULL);
            SET_PTR(SUCC_PTR(ptr),NULL);
            //update the root of free list at the index
            free_lists[index]=ptr;
        }
    }
    return;

}
//delete the node in the segregated free list to input ( if the pointer is in the list 2, after delete and insert again in the 5th list)
static void delete_node(void * ptr)
{
    int index;
    int size= GET_SIZE(HDRP(ptr));

    //select segregated list
    while((index < LIST-1  ) && (size >1) )
    {
        size = size >>1;
        index++;
    }

    //the pointer is not the head of the doubly linked list
    if(PRED(ptr) != NULL)
    {
        //the pointer is not at the end of the doubly linked list
        if(SUCC(ptr) != NULL)
        {
            //link the successor and predessor of the pointer
            SET_PTR(SUCC_PTR(PRED(ptr)) , SUCC(ptr));
            SET_PTR(PRED_PTR(SUCC(ptr)) , PRED(ptr));
        }
        //the pointer is at the end
        else
        {
            SET_PTR(SUCC_PTR(PRED(ptr)), NULL);
            free_lists[index] = PRED(ptr);
        }
    }
    //the pointer at the beginning
    else
    {
        //the list has 2 nodes
        if(SUCC(ptr) !=NULL)
        {
            SET_PTR(PRED_PTR(SUCC(ptr)),NULL);
        }
        else
        {
            free_lists[index]=NULL;
        }
    }
    return;
}

//expand the free block and input to the segregated free list
static void * coalesce(void * ptr)
{
    //check if the prevrious block is allocated
    size_t prev_all =GET_ALLOC(HDRP(PREV_BLKP(ptr)));
    //check if the next block is allocated
    size_t next_all =GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
    size_t size =GET_SIZE(HDRP(ptr));

    //if the previous is reallocated, do not coalesce
    if(GET_TAG(HDRP(PREV_BLKP(ptr))) == 1)
        prev_all = 1;

    //cannot coalesce with previous and the next block
    if(prev_all == 1 && next_all ==1)
        return ptr;

    //can coalesce with the next block
    if(prev_all == 1 && next_all == 0)
    {
        delete_node(ptr);
        delete_node(NEXT_BLKP(ptr));
        //the new size of the coalesce free block
        size += GET_SIZE(HDRP(NEXT_BLKP(ptr)));
        //update the info at the header and the footer of the new free block at the pointer
        PUT(HDRP(ptr), PACK(size,0));
        PUT(FTRP(ptr), PACK(size,0));
    }
    //coalesce with the previous block
    else if(prev_all == 0 && next_all == 1)
    {
        delete_node(ptr);
        delete_node(PREV_BLKP(ptr));
        size+= GET_SIZE(HDRP(PREV_BLKP(ptr)));
        ptr= PREV_BLKP(ptr);
        PUT(HDRP(ptr), PACK(size,0));
        PUT(FTRP(ptr), PACK(size,0));
    }
    //coalesce with both previous and next block
    else if (prev_all ==0 && next_all ==0)
    {
        delete_node(ptr);
        delete_node(PREV_BLKP(ptr));
        delete_node(NEXT_BLKP(ptr));

        size+= GET_SIZE(HDRP(PREV_BLKP(ptr))) + GET_SIZE(HDRP(NEXT_BLKP(ptr)));

        ptr = PREV_BLKP(ptr);
        PUT(HDRP(ptr), PACK(size,0));
        PUT(FTRP(ptr), PACK(size,0));   
    }
    //insert the new free list to the segregated free list
    insert_node(ptr,size);
    return ptr;
}


//place the size in the appropriate block in the free list and decide to whether it is needed to split the block
//return the pointer to the new allocated block
static void * place(void * ptr, size_t asize)
{
    size_t size = GET_SIZE(HDRP(ptr));
    size_t remain = size - asize;

    delete_node(ptr);

    if(remain <= DSIZE*2)
    {
        //do not split
        PUT(HDRP(ptr), PACK(size,1));
        PUT(FTRP(ptr), PACK(size,1));
    }

    else if(asize >= 100)
    {
        //split block
        PUT(HDRP(ptr), PACK(remain,0));
        PUT(FTRP(ptr), PACK(remain,0));
        //put the allocated block at the end of the free block
        PUT_NOTAG(HDRP(NEXT_BLKP(ptr)), PACK(asize,1));
        PUT_NOTAG(FTRP(NEXT_BLKP(ptr)), PACK(asize,1));
        //insert the remainder free block to segregated free list
        insert_node(ptr,remain);
        return NEXT_BLKP(ptr);
    }
    //put the allocated block at the beginning of the free block
    else
    {
        //split block
        PUT(HDRP(ptr), PACK(asize,1));
        PUT(FTRP(ptr), PACK(asize,1));
        PUT_NOTAG(HDRP(NEXT_BLKP(ptr)), PACK(remain,0));
        PUT_NOTAG(FTRP(NEXT_BLKP(ptr)), PACK(remain,0));
        insert_node(NEXT_BLKP(ptr),remain);
    }
    return ptr;
}

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
	int index;

	free_lists = (void**)malloc(sizeof(void*) * LIST);

    //initialize the segregated free list NULL
    for(index=0;index< LIST; index++)
	//*free_lists + index = NULL;
        free_lists[index] = NULL;

    char * heap;
    //cannot allocated the heap
    if((long)(heap = mem_sbrk(4 * WSIZE)) == -1)
        return  -1;
    //padding
    PUT_NOTAG(heap, 0);
    //input the prologue header
    PUT_NOTAG(heap + 1* WSIZE, PACK(DSIZE,1));
    //prologue footer
    PUT_NOTAG(heap + 2* WSIZE, PACK(DSIZE,1));
    //epilogue header
    PUT_NOTAG(heap + 3* WSIZE, PACK(0,1));


    if(extend_heap(INITCHUNKSIZE)==NULL){
        return -1;

	}

	return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    if(size==0)
        return NULL;

    size_t newsize ; //adjust size
    size_t extend; //extend heap if neccessary
	void * p = mem_sbrk(newsize);
	
    //align block size
    if( size <= SIZE_T_SIZE)
    {
        newsize = 2*SIZE_T_SIZE;
    }
    else
    {
        newsize =ALIGN(size + SIZE_T_SIZE);
    }

    int index=0;
    size_t search = newsize;
    //traverse the segregated free list
    while(index < LIST)
    {
        //find the appropriate free list
        if((index == LIST -1) || (search <= 1 && free_lists[index] != NULL))
        {
            p = free_lists[index];
            //ignore the block with reallcation bit and find the smallest different size block
            while(p !=NULL  && ((newsize > GET_SIZE(HDRP(p)) || GET_TAG(p))))
            {
                p = PRED(p);
            }
            //can find the free block
            if(p != NULL)
                break;
        }
        search = search >>1;
        index ++;
    }
    //expand the heap to allocate
    if(p == NULL)
    {
        extend = MAX(newsize,CHUNKSIZE);
        //cannot extend the heap
        p = extend_heap(extend);
        if(p == (void *)-1)
            return NULL;
    }
	/*
	   else {
	   	*(size_t *)p = size;
		return (void *)((char *)p + SIZE_T_SIZE);
		}
	*/
    //place and divide block to the memory
    p = place(p,newsize);

    //return pointer to the allocated block
    return p;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
		size_t size = GET_SIZE(HDRP(ptr));

		REMOVE_RATAG(HDRP(NEXT_BLKP(ptr)));
		
		PUT(HDRP(ptr), PACK(size, 0));
		PUT(FTRP(ptr), PACK(size, 0));
		
		insert_node(ptr,size);
		
		coalesce(ptr);
}


/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
/*
	if(size == 0 )
        return NULL;

    void *newptr = ptr;
    void *newptr;
	int remain;
    size_t copySize = size;
	int blockbuff;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    copySize = *(size_t *)((char *)newptr - SIZE_T_SIZE);
    if (size < copySize)
      copySize = size;
    memcpy(newptr, newptr, copySize);
    mm_free(newptr);
    return newptr;*/

	void *oldptr = ptr;
	void *newptr;    /* Pointer to be returned */
    size_t copySize = size; /* Size of new block */
    int remainder;          /* Adequacy of block sizes */
    int extendsize;         /* Size of heap extension */
    int block_buffer;       /* Size of block buffer */
    
	newptr = ptr;
    // Ignore size 0 cases
    if (size == 0)
        return NULL;
    
    // Align block size
    if (copySize <= DSIZE) {
        copySize = 2 * DSIZE;
    } else {
        copySize = ALIGN(size+DSIZE);
    }
    
    /* Add overhead requirements to block size */
    copySize += REALLOC_BUFFER;
    
    /* Calculate block buffer */
    block_buffer = GET_SIZE(HDRP(ptr)) - copySize;
    
    /* Allocate more space if overhead falls below the minimum */
    if (block_buffer < 0) {
        /* Check if next block is a free block or the epilogue block */
        if (!GET_ALLOC(HDRP(NEXT_BLKP(ptr))) || !GET_SIZE(HDRP(NEXT_BLKP(ptr)))) {
            remainder = GET_SIZE(HDRP(ptr)) + GET_SIZE(HDRP(NEXT_BLKP(ptr))) - copySize;
            if (remainder < 0) {
                extendsize = MAX(-remainder, CHUNKSIZE);
                if (extend_heap(extendsize) == NULL)
                    return NULL;
                remainder += extendsize;
            }
            
            delete_node(NEXT_BLKP(ptr));
            
            // Do not split block
            PUT_NOTAG(HDRP(ptr), PACK(copySize + remainder, 1)); 
            PUT_NOTAG(FTRP(ptr), PACK(copySize + remainder, 1)); 
        } else {
            newptr = mm_malloc(copySize - DSIZE);
            memcpy(newptr, ptr, MIN(size, copySize));
            mm_free(ptr);
        }
        block_buffer = GET_SIZE(HDRP(newptr)) - copySize;
    }
    
    // Tag the next block if block overhead drops below twice the overhead 
    if (block_buffer < 2 * REALLOC_BUFFER)
        SET_RATAG(HDRP(NEXT_BLKP(newptr)));
    
    // Return the reallocated block 
    return newptr;
}
