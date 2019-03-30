/*
 * mm.c
 *
 * This is the only file you should modify.
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
#define DEBUG
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif


/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8
#define WSIZE       4       /* word size (bytes) */  
#define DSIZE       8       /* doubleword size (bytes) */
#define CHUNKSIZE  (1<<8)  /* initial heap size (bytes) */
#define OVERHEAD    8       /* overhead of header and footer (bytes) */

#define MAX(x, y) ((x) > (y)? (x) : (y))  

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p */
/* NB: this code calls a 32-bit quantity a word */
#define GET(p)       (*(unsigned int *)(p))
#define PUT(p, val)  (*(unsigned int *)(p) = (val))  

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)  
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))
/* $end mallocmacros */

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)


static char *heap_listp = 0;  
static void *seg_listp; 
#define SEG_LIST_COUNT 16

#define PUT_ADDR(p, addr) (*(unsigned long long *)(p)=(unsigned long long)(addr))


#define GET_PREV(p) ((char *)p)
#define GET_NEXT(p) ((char *)p + DSIZE)


#define GET_PREV_BLK(p) (*(char **)(p))
#define GET_NEXT_BLK(bp)   (*(char **)(GET_NEXT(bp)))




static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void remove_free_block(void *bp);

static void insert_free_block(void *bp, size_t block_size);
/* static void printblock(void *bp); 
static void checkblock(void *bp); */

/* helper funtion to modify address, get the thing in the address, mainly used for seg list */
#define ADDR_CHANGE(p, index) *((char **)p + index)


int mm_init(void) {
    seg_listp=mem_sbrk(SEG_LIST_COUNT*DSIZE);

    for (int i=0; i < SEG_LIST_COUNT; i++) {
    	ADDR_CHANGE(seg_listp, i)=NULL;
    }

    if ((heap_listp = mem_sbrk(4*WSIZE)) == NULL)
    	return -1;
  	PUT(heap_listp, 0);                        /* alignment padding */
  	PUT(heap_listp+WSIZE, PACK(OVERHEAD, 1));  /* prologue header */ 
  	PUT(heap_listp+DSIZE, PACK(OVERHEAD, 1));  /* prologue footer */ 
  	PUT(heap_listp+WSIZE+DSIZE, PACK(0, 1));   /* epilogue header */
  	
  	heap_listp += DSIZE;
  	mm_checkheap(1);
  	if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
    	return -1;
  	return 0;

}


void *mm_malloc (size_t size) {
    size_t asize;
    
    mm_checkheap(1);

    if (size==0) {
    	return NULL;
    }

    if (size <= 2*DSIZE) {
    	asize = 2*DSIZE+2*WSIZE;
    }
    else {
    	asize = ((size + DSIZE - 1) / DSIZE)*DSIZE + 2*WSIZE; 
    }
    size_t extendsize;
    char *bp;

    if ((bp=find_fit(asize)) !=NULL) {
    	place(bp, asize);
	    return bp;
    }

    extendsize=MAX(asize,CHUNKSIZE);
    if ((bp=extend_heap(extendsize/WSIZE)) ==NULL) {
    	return NULL;
    }	
    place(bp,asize);
    return bp;
    
}


void mm_free (void *bp) {
    if (bp==NULL) {
    	return;
    }
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp),PACK(size,0));
    PUT(FTRP(bp),PACK(size,0));
    insert_free_block(bp,size);
    coalesce(bp);
}


void *mm_realloc(void *ptr, size_t size)
{
  size_t oldsize;
  void *newptr;

  
  if(size == 0) {
    mm_free(ptr);
    return 0;
  }

 
  if(ptr == NULL) {
    return mm_malloc(size);
  }

  newptr = mm_malloc(size);

  
  if(!newptr) {
    return 0;
  }

  
  oldsize = GET_SIZE(HDRP(ptr));
  if(size < oldsize) oldsize = size;
  memcpy(newptr, ptr, oldsize);

  
  mm_free(ptr);

  return newptr;
}


void *mm_calloc (size_t nmemb, size_t size) {
    size_t bytes = nmemb * size;
  	void *newptr;

  	newptr = mm_malloc(bytes);
  	memset(newptr, 0, bytes);

  	return newptr;
}



static void *extend_heap(size_t words) 
{
  
  char *bp;
  size_t size;
  

  
  size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
  if ((long)(bp = mem_sbrk(size)) < 0) 
    return NULL;

  
  PUT(HDRP(bp), PACK(size, 0));       
  PUT(FTRP(bp), PACK(size, 0));       
  PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); 

  
  insert_free_block(bp,size);
  
  return coalesce(bp);
}


static void *find_fit(size_t asize)
{   
    size_t size = asize;
    int i = 0;
    void *list_ptr = NULL;
 
    while (i < SEG_LIST_COUNT) {
	
    	if ((i == SEG_LIST_COUNT - 1) || ((size <= 1) && (ADDR_CHANGE(seg_listp, i)!= NULL))) {
       		list_ptr  = ADDR_CHANGE(seg_listp, i);

			    while ((list_ptr != NULL) && (asize > GET_SIZE(HDRP(list_ptr)))){
          			list_ptr = GET_NEXT_BLK(list_ptr);
        		}
        	if (list_ptr != NULL) {
         		break;
        	}
      }
      i++;
      size = size >> 1;
    }
    return list_ptr;  
}


static void place(void *bp, size_t asize)
  
{
  	size_t csize = GET_SIZE(HDRP(bp));   
  	remove_free_block(bp);

  	if ((csize - asize) >= (2*DSIZE + OVERHEAD)) { 
    	PUT(HDRP(bp), PACK(asize, 1));
    	PUT(FTRP(bp), PACK(asize, 1));
    	bp = NEXT_BLKP(bp);
    	PUT(HDRP(bp), PACK(csize-asize, 0));
    	PUT(FTRP(bp), PACK(csize-asize, 0));
  		insert_free_block(bp,csize-asize);
  		coalesce(bp);	
  	}
  	else { 
    	PUT(HDRP(bp), PACK(csize, 1));
    	PUT(FTRP(bp), PACK(csize, 1));
  	}
}


static void insert_free_block(void *bp, size_t block_size)
{
	void *list_ptr = NULL;
	int i=0;
	while ((i< (SEG_LIST_COUNT -1)) && (block_size > 1)) {
		block_size=block_size >> 1;
		i++;
	}	  
	list_ptr=ADDR_CHANGE(seg_listp, i);
	if (list_ptr!=NULL) {
		char* temp=list_ptr;
		ADDR_CHANGE(seg_listp,i)=bp;
		PUT_ADDR(GET_PREV(bp), NULL);
		PUT_ADDR(GET_NEXT(bp), temp);
		PUT_ADDR(GET_PREV(temp), bp);
		
	}
	else {
		ADDR_CHANGE(seg_listp,i)=bp;
		PUT_ADDR(GET_PREV(bp), NULL);
		PUT_ADDR(GET_NEXT(bp), NULL);
	}
}


static void remove_free_block(void *bp)
{ 
  	int i = 0; 
  	size_t block_size = GET_SIZE(HDRP(bp));
  
  
  	if (GET_PREV_BLK(bp) == NULL) {
  
    	while (i < (SEG_LIST_COUNT - 1) && block_size > 1) {
      		block_size = block_size >> 1;
      		i++;
    	}
    	ADDR_CHANGE(seg_listp, i)= GET_NEXT_BLK(bp);
    	if (ADDR_CHANGE(seg_listp, i) != NULL) {
      		PUT_ADDR(GET_PREV(ADDR_CHANGE(seg_listp, i)), NULL);
    	}
    	return;
  	}
  
  	
  	PUT_ADDR(GET_NEXT(GET_PREV_BLK(bp)), GET_NEXT_BLK(bp)); 
  	if (GET_NEXT_BLK(bp) != NULL) {
    	PUT_ADDR(GET_PREV(GET_NEXT_BLK(bp)), GET_PREV_BLK(bp));
  	} 
}

static void *coalesce(void *bp)
{
  size_t prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(bp)));
  size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
  size_t size = GET_SIZE(HDRP(bp));
   
  if (prev_alloc && next_alloc) {		
    return bp;
  } 
  else if (prev_alloc && !next_alloc) {		
    remove_free_block(bp);
    remove_free_block(NEXT_BLKP(bp));
    size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
  }
  
  else if (!prev_alloc && next_alloc) { 	
    remove_free_block(bp);
    remove_free_block(PREV_BLKP(bp));
    size += GET_SIZE(HDRP(PREV_BLKP(bp)));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    bp = PREV_BLKP(bp);
  }

  else {					
    remove_free_block(PREV_BLKP(bp));
    remove_free_block(bp);
    remove_free_block(NEXT_BLKP(bp));
    size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
    bp = PREV_BLKP(bp);
  }


  insert_free_block(bp, size);
  return bp;
}







static void printblock(void *bp) 
{
  size_t hsize, halloc, fsize, falloc;

  hsize = GET_SIZE(HDRP(bp));
  halloc = GET_ALLOC(HDRP(bp));  
  fsize = GET_SIZE(FTRP(bp));
  falloc = GET_ALLOC(FTRP(bp));  

  
  if (hsize == 0) {
    printf("%p: EOL\n", bp);
    return;
  }

   printf("%p: header: [%p:%c] footer: [%p:%c]\n", bp, 
      (void *) hsize, (halloc ? 'a' : 'f'), 
      (void *) fsize, (falloc ? 'a' : 'f')); 

   if (GET_ALLOC(HDRP(bp))==0) {
       char* a=(char*) GET_PREV_BLK(bp);
       char* b=(char*) GET_NEXT_BLK(bp);
   	 	if (!a) {
   	 		printf("NULL\n");

   	 	}
   		else {
   			printf("%p\n",a);
   		}
   		if (!b) {
   			printf("NULL\n");
   		}
   		else {
   			printf("%p\n",b);
   		}

   }	

}

static void checkblock(void *bp) 
{
  if ((size_t)bp % 8)
    printf("Error: %p is not doubleword aligned\n", bp);
  if (GET(HDRP(bp)) != GET(FTRP(bp)))
    printf("Error: header does not match footer\n");
}









 
void mm_checkheap(int verbose)
{
  return;
  char *bp = heap_listp;

  if (verbose)
    printf("Heap (%p):\n", heap_listp);

  if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp)))
    printf("Bad prologue header\n");
  checkblock(heap_listp);

  for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
    if (verbose) 
      printblock(bp);
    checkblock(bp);
  }

  if (verbose)
    printblock(bp);
  if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
    printf("Bad epilogue header\n");
}
