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
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "FlipFlopOlympians",
    /* First member's full name */
    "Nick Karlovich",
    /* First member's email address */
    "karlo015@umn.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 16

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0xf)

#define WSIZE 8
#define DSIZE 16
#define CHUNKSIZE (1<<12)
#define OVERHEAD 16

#define MAX(x,y) ((x) > (y) ? (x) : (y))

#define PACK(size, alloc) ((size) | (alloc))

/* read and write a word at address p */
#define GET(p)       (*(size_t *)(p))
#define PUT(p, val)  (*(size_t *)(p) = (val))

/* read the size and allocated fields from address p
   GET_SIZE returns size of entire block including header and footer  */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
#define GET_NULL(p) (((GET(p) & 0x2)) >> 1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))
/* Given block ptr bp, (not the header the bit after header before data)
        return the pointer that is in the first bit of data, ie when the
        block is free return a pointer */
//#define NEXT_NODE(bp) ((char *)GET(bp))
#define NEXT_NODE(bp) ((char *)GET(bp))

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
static char *heap_listp;
#ifdef NEXT_FIT
static char *rover;
#endif
/*
   Size Class Pointers
   These are measuring in WSIZE so
   scp_1 is a 1 word block of 8 bytes
   the struct itself is just a pointer to the first instance of such a block in the heap
*/

/*
NOTE: Pointers, atleast char* are 8 bytes long or
one wordsize ie WSIZE
*/

/*
the number of pointers here that need to have space allocated
for them on the stack on heap initialization.
*/

static int num_of_size_class_p = 19;

static char *scp_1;
static char *scp_2;
static char *scp_3;
static char *scp_4;
static char *scp_5;
static char *scp_6;
static char *scp_7;
static char *scp_8_15;
static char *scp_16_31;
static char *scp_32_63;
static char *scp_64_127;
static char *scp_128_255;
static char *scp_256_511;
static char *scp_512_1k;//512 - 1023
static char *scp_1k_2k;// 1024 - 2047
static char *scp_2k_4k;// 2048 - 4095
static char *scp_4k_8k;//4096 - 8191
static char *scp_8k_16k;//8192 - 16383
static char *scp_16k_32k;//16384 - 32767


static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void printblock(void *bp);
static void checkblock(void *bp);
int mm_check(int verbose);
static void add_node(void *root, void *bp);
static void add_node_to_root(size_t size, void *p);
static void remove_node(size_t size, void *p);
static size_t get_size_class(size_t b_size);
static void *get_root(size_t size_class);
static void *next_node(void *bp);
static char *get_node_address(void *cp);

static int debug = 1;
//static char *brk;


/*

x is either 0 if free or 1 if allocated
the remainder of bits is to determine size of item allocated

Allocated

63                                                 0
 +-------------------------------------------------+
 |  Size                                       |--x|   Header
 +-------------------------------------------------+  <=  bp
 |                                                 |
 |               payload and padding               |
 |                                                 |
 +-------------------------------------------------+
 |  Size                                       |--x|
 +-------------------------------------------------+

Free Blocks
+-------------------------------------------------+
|  Size of this block                         |--x|   Header
+-------------------------------------------------+  <=  bp
|             Pointer to Successor in Seg list    |
|                                                 |
|                                                 |
+-------------------------------------------------+
|  Size                                       |--x|
+-------------------------------------------------+



/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    if((heap_listp = mem_sbrk(4 * WSIZE)) == NULL) {
        return -1;
    }
    PUT(heap_listp, 0);
    PUT(heap_listp + WSIZE, PACK(OVERHEAD, 1)); //prologue header
    PUT(heap_listp + DSIZE, PACK(OVERHEAD, 1)); //prologue footer
    printf("\n%p heap_listp, heap_list + WSIZE: %p\n",heap_listp, heap_listp + WSIZE);
    PUT(heap_listp + WSIZE + DSIZE, PACK(0,1)); //epilogue header
    heap_listp += DSIZE;


    #ifdef NEXT_FIT
        rover = heap_listp;
    #endif
    /*
    //scp_1 = mm_malloc(sizeof(scp_1));
    // scp_2 = mm_malloc(sizeof(scp_1));
    // scp_3 = mm_malloc(sizeof(scp_1));
    // scp_4 = mm_malloc(sizeof(scp_1));
    // scp_5 = mm_malloc(sizeof(scp_1));
    // scp_6 = mm_malloc(sizeof(scp_1));
    // scp_7 = mm_malloc(sizeof(scp_1));
    // scp_8_15 = mm_malloc(sizeof(scp_1));
    // scp_16_31 = mm_malloc(sizeof(scp_1));
    // scp_32_63 = mm_malloc(sizeof(scp_1));
    // scp_64_127 = mm_malloc(sizeof(scp_1));
    // scp_128_255 = mm_malloc(sizeof(scp_1));
    // scp_256_511 = mm_malloc(sizeof(scp_1));
    // scp_512_1k = mm_malloc(sizeof(scp_1));
    // scp_1k_2k = mm_malloc(sizeof(scp_1));
    // scp_2k_4k = mm_malloc(sizeof(scp_1));
    // scp_4k_8k = mm_malloc(sizeof(scp_1));
    // scp_8k_16k = mm_malloc(sizeof(scp_1));
    // scp_16k_32k = mm_malloc(sizeof(scp_1));
    // printf("SCP 1 %p : \n",scp_1);


    //printf("heap high, heap low? AFTER: %d,   %d\n",mem_heap_hi(), mem_heap_lo());
    //printf("size: %d\n",GET_SIZE(HDRP(scp_1)));
    //printf("point: %p\n",scp_1);


    //if(debug) {
        //printf("TEST 1: \n");
        //add_node(3488, NULL);

        printf("TEST 2: \n");
        add_node(2, NULL);
        printf("TEST 1: \n");
        add_node(3, NULL);
        printf("TEST 2: \n");
        add_node(4, NULL);
        printf("TEST 1: \n");
        add_node(5, NULL);
        printf("TEST 2: \n");
        add_node(6, NULL);
        printf("TEST 1: \n");
        add_node(7, NULL);
        printf("TEST 2: \n");
        add_node(8, NULL);
        printf("TEST 1: \n");

        add_node(9, NULL);
        printf("TEST 2: \n");
        add_node(10, NULL);
    //}
    //mm_check(debug);
    */
    //printf("BEFORE FIRST EXTEND\n");
  //  mm_check(debug);
  int count = 0;
  mm_check(debug);
    extend_heap(num_of_size_class_p * 4);//76 blocks

    //printf("AFTER FIRST EXTEND\n");

    mm_check(debug);
    printf("\n%p heap_listp, heap_list + WSIZE: %p\n",heap_listp, heap_listp + WSIZE);
    for(char* i = heap_listp + WSIZE; i < heap_listp + 600; i = i + 8) {
        printf("p: %p\n",i);
        PUT(i,0);
        count++;
    }
    PUT(heap_listp + WSIZE, PACK(608,1));       //start of root index's
    PUT(heap_listp + 608, PACK(608,1));         //end of roots index's
    printf("Counter: %d\n", count);
    mm_check(debug);

    //printf("heap high, heap low? BEFORE : %d,   %d\n",mem_heap_hi(), mem_heap_lo());
    printf("\n%p heap_listp, heap_list + WSIZE: %p\n",heap_listp, heap_listp + WSIZE);
    scp_1 = heap_listp + 32 * 0 + DSIZE;
    scp_2 = heap_listp + 32 * 1 + DSIZE;
    scp_3 = heap_listp + 32 * 2 + DSIZE;
    scp_4 = heap_listp + 32 * 3 + DSIZE;
    scp_5 = heap_listp + 32 * 4 + DSIZE;
    scp_6 = heap_listp + 32 * 5 + DSIZE;
    scp_7 = heap_listp + 32 * 6 + DSIZE;
    scp_8_15 = heap_listp + 32* 7 + DSIZE;
    scp_16_31 = heap_listp + 32 * 8 + DSIZE;
    scp_32_63 = heap_listp + 32 * 9 + DSIZE;
    scp_64_127 = heap_listp + 32 * 10 + DSIZE;
    scp_128_255 = heap_listp + 32 * 11 + DSIZE;
    scp_256_511 = heap_listp + 32 * 12 + DSIZE;
    scp_512_1k = heap_listp + 32 * 13 + DSIZE;
    scp_1k_2k = heap_listp + 32 * 14 + DSIZE;
    scp_2k_4k = heap_listp + 32 * 15 + DSIZE;
    scp_4k_8k = heap_listp + 32 * 16 + DSIZE;
    scp_8k_16k = heap_listp + 32 * 17 + DSIZE;
    scp_16k_32k = heap_listp + 32 * 18 + DSIZE;




printf("\nscp_1: %p\n heap_listp : %p \n",scp_1, heap_listp);
    printf("\nscp_2: %p\n",scp_2);
    printf("\nscp_3: %p\n",scp_3);
    printf("\nscp_4: %p\n",scp_4);
      printf("\nscp_5: %p\n",scp_5);
      printf("\nscp_6: %p\n",scp_6);
      printf("\nscp_7: %p\n",scp_7);
      printf("\nscp_8: %p\n",scp_8_15);
      printf("\nscp_16: %p\n",scp_16_31);
      printf("\nscp_32: %p\n",scp_32_63);
      printf("\nscp_64: %p\n",scp_64_127);
      printf("\nscp_128: %p\n",scp_128_255);
      printf("\nscp_256: %p\n",scp_256_511);
      printf("\nscp_512: %p\n",scp_512_1k);
      printf("\nscp_1k: %p\n",scp_1k_2k);
      printf("\nscp_2k: %p\n",scp_2k_4k);
      printf("\nscp_4k: %p\n",scp_4k_8k);
      printf("\nscp_8k: %p\n",scp_8k_16k);
      printf("\nscp_16k: %p\n",scp_16k_32k);




    if(extend_heap(CHUNKSIZE/WSIZE) == NULL) {
        printf("extend_heap == null in init:\n");
        return -1;
    } else {
        if(debug) {
            printf("HEAP EXTENDED\n");
        }
    }


    return 0;
}

static size_t do_arith(size_t size) {
    int counter = 0;
    size_t num = size;
    //printf("\nNUM: 0x%x %ld\n", num, num);
    num = num >> 3;
  //  printf("     ~\nNUM: 0x%x %ld\n", num, num);
  //  printf("SIZE: %ld",size);

    //takes a number at least 8
    while(!((num & 0x1) == num) && num != 0) {
        num = num >> 1;
    //    printf("\nloopNUM: 0x%x %ld\n", num, num);
    //    printf("Counter: %d", counter);
        counter++;
    }
    if(num == 0) {
        printf("something went wrong\n");
        return -1;
    } else {
        return counter;
    }

}

static void remove_node(size_t size, void *bp) {
  void *ptr = NULL;
  char *secNodeAddress = 1;
  size_t abc = get_size_class(size);
  ptr = get_root(abc);
  //void *head = HDRP(ptr);
  //we have the root pointer
  //next we need to get the pointer of the 1st non root element
  //then we need to set 2nd item in root class to be the second one.
  secNodeAddress = next_node(ptr);
  secNodeAddress = get_node_address(secNodeAddress);
  //secNodeAddress = (char *)((GET(NEXT_NODE(ptr))));
  PUT(ptr, secNodeAddress);
  printf("removed free node of %ld from size class %ld\n",size,abc);
}

static size_t get_size_class(size_t b_size) {
  size_t size_class = b_size;
  switch (b_size) {
      case 1:
      size_class = 0;
      break;

      case 2:
      size_class = 1;
      break;

      case 3:
      size_class = 2;
      break;

      case 4:
      size_class = 3;
      break;

      case 5:
      size_class = 4;
      break;

      case 6:
      size_class = 5;
      break;

      case 7:
      size_class = 6;
      break;

      default:
      size_class = 7 + do_arith(b_size);
  }
  return size_class;
}

//returns pointer to first value of root block
static void *get_root(size_t size_class) {
  return ((void *)((scp_1 + (sizeof(scp_1) * 4 * size_class))));
}

static void *next_node(void *bp) {
  void *thing;
  if((thing = (void *)GET(bp)) == NULL) {
    return NULL;
  } else {
    return thing;
  }
}

//basically next function for getting next_node's memory value if it exists
static char *get_node_address(void *cp) {
  if(cp == NULL) {
    return NULL;
  } else {
    return GET(cp);
  }
}

static int is_root_list_empty(void *root) {
  void *a = next_node(root);
  //char *a = ((char *)(GET(NEXT_NODE(root))));
  if(a == NULL) {
    return 1;
  } else {
    return 0;
  }
}

static void add_node(void *root, void *bp) {
  void *first = NEXT_NODE(root);
  //set what root is pointing at to the pointer inside the block we have
  void *valptr = bp + WSIZE;
  //valptr now points at the first value in the block
  PUT(valptr,(char *) first);
  //we have now set the first variable in bp to the address that the root pointer
  //originally pointed to.
  //set what root is pointing at to the block we have
  PUT(root,(char *)bp);
}

/* p is a block pointer
 * this function adds free blocks to their class lists
 */
static void add_node_to_root(size_t size, void *bp) {
  void *ptr = NULL;
  size_t size_class = 0;
  // this statement determines what size class the node fits in.
  //moved to get_size_class
  //printf("SIZE OF NODE BEING ADDED: %ld\n",size);
  size_class = get_size_class(size);
  //printf("size class: %ld\n", size_class);
  //printf("size class: %d\n",size_class);
  //printf("size of scp_1 %d\n",sizeof(scp_1));

  //this line gets the root sizeclass node created and malloc and returns a pointer
  //to the front of the pointer inside that bit.
  ptr = get_root(size_class);
  //replaced by get_root(size_class);
  //ptr = (void *)((scp_1 + (sizeof(scp_1) * 4 * size_class)) + WSIZE);
  /* ptr now points as such

  +-----------------------------------+
  | HEADER STUFF    (of size class x) |
  +-----------------------------------+  <--- ptr
  |Pointer to next node in class size |
  +-----------------------------------+
  |          FOOTER STUFF             |
  +-----------------------------------+
  */
  //printf("head: %p\n", heap_listp);
  //printf("void boi: %p\n", ptr);
  //mm_check(1);
  /*
      determine what size class the new block should go into         DONE

      add it to that size class by ...
      taking that block, setting the pointer spc_# to *p             DONE
      and setting *p's next block in list pointer to what spc_# was  DONE
      previously looking at.
  */

  //if the root node is looking at nothing then make what it is currently looking at
  //the node that was added.

  /*

  The problem I'm currently running into is that
  my root list only can hold one element, ie it doesn't continue to search the list
  of elements that I've created so in the example currently there is a free block
  sized 2128 in size class 15 the same as the mm_malloc() request of 4096,  Thus the program
  tries to use the size 2128 block of free'd data its locaiton for a block of 4096 data which
  wont work.  SO
  TO FIX THIS:
  currently it just checks if a pointer exists,
    ->> it needs to check if pointer exists, then if the block that exists is a size >= to the block
    that is being malloc'd.  If as in our example the block in the list is say 2128 but we want 4096,
    then the next step is to have the ptr look and see if the (1st) block has a pointer to a Second
    block in that size class if it does then go to that one and repeat, if it doesn't, then go to
    the next biggest size class.  There is the posibility of sorting such values as they are added
    to the root list but thats a feature for later

  if(size_class has a block) {
      if(that block the correct size) {
        perfect! we're done
      } else {
          if(does that block have a pointer to next block?) {
            YES: go to that block and repeat previous steps
          } else {
            NO: end of list, go to next root class
          }
      }
  } else {
    Go to next root block
  }
  */
  if(!is_root_list_empty(ptr)) {
    PUT(ptr, (char *)bp);
  } else {
    // //[ root ] ->   [1st element]
    // //get what root is pointing at.
    // void *first = NEXT_NODE(ptr);
    // //set what root is pointing at to the pointer inside the block we have
    // void *valptr = bp + WSIZE;
    // //valptr now points at the first value in the block
    // PUT(valptr,(char *) first);
    // //we have now set the first variable in bp to the address that the root pointer
    // //originally pointed to.
    // //set what root is pointing at to the block we have
    // PUT(ptr,(char *)bp);

    add_node(ptr,bp);
  }
  printf("added free node of %ld to size class %ld\n",size,size_class);
  //printf("GET: %ld\n",GET(ptr));
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 * multiple in this context means 1 block or 8 bytes, our size class is still 1 block ie
 * 8 bytes, 2 block is 16 bytes + OVERHEAD
 */
void *mm_malloc(size_t size)
{
    size_t asize;      /* adjusted block size */
    size_t extendsize; /* amount to extend heap if no fit */
    char *bp;

    /* Ignore spurious requests */
    if (size <= 0) {
        if(debug) {
            printf("Malloc Request of <=0, ignored");
        }
	   return NULL;
    }

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE) {
	   asize = DSIZE + OVERHEAD;
    } else {
	   asize = DSIZE * ((size + (OVERHEAD) + (DSIZE-1)) / DSIZE);
    }
    if(debug) {
        printf("Malloc Op of Size asize: %ld\n", asize);
    }
    //printf("Malloc Check\n");
    //mm_check(debug);

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        if(debug) {
            printf("found w/out extending, next 'free mm_check from place in malloc'\n");
        }
    	place(bp, asize);


    	return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);
    if((bp = extend_heap(extendsize/WSIZE)) == NULL) {
        if(debug) {
            printf("Out of Memory: Malloc\n");
        }
    	return NULL;
    }
    if(debug) {
        printf("found w/extending\n");
    }
    printf("\n 2nd malloc mm_free check '' '' \n");
    place(bp, asize);
    printf("\n Malloc mm_check \n");
    mm_check(debug);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{

  ptr = coalesce(ptr);
  int size = GET_SIZE(HDRP(ptr));
  printf("Size of free'd block: %d\n", size);

  PUT(HDRP(ptr), PACK(size,0));
  PUT(FTRP(ptr), PACK(size,0));

  //to clear up first 8 bytes of free'd block so that a pointer can be set there,
  //while also keeping it null for when added to class list
  PUT(ptr,0);
  //size = GET_SIZE(HDRP(ptr));
  add_node_to_root(size, ptr);
  printf("Free mm_check \n");
  mm_check(debug);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;

    newptr = mm_malloc(size);
    if (newptr == NULL) {
        return NULL;
    }
    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}

/*
 * mm_check - Return 1 if the heap is consistent.
 TODO: copied this, make it better
 */
 int mm_check(int verbose)
 {
     char *bp = heap_listp;

     if (verbose)
 	//printf("Heap (%p):\n", heap_listp);

     if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp))) {
         printf("%d + %d\n",(int)(GET_SIZE(HDRP(heap_listp))), DSIZE);
         printf("%d\n",(int)(GET_ALLOC(HDRP(heap_listp))));
         printf("Bad prologue header\n");
   }
     checkblock(heap_listp);

     for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
     	if (verbose)
     	    printblock(bp);
     	checkblock(bp);
     }

     if (verbose)
 	printblock(bp);
     if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp)))) {
       printf("Bad epilogue header\n");
       printf("%d ",GET_SIZE(HDRP(bp)));
       printf(" %d \n", GET_ALLOC(HDRP(bp)));
     }

     return 1;
 }

static void *extend_heap(size_t words) {
    char *bp;
    size_t size;

    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    //size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    // bp = mem_sbrk(size);
    // if(bp == (void *)-1) {
    //     return NULL;
    // }

    if((bp = mem_sbrk(size)) == (void *)-1) {
        if(debug) {
            printf("extend_heap failed\n");
        }
        return NULL;
    }

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1));

    return coalesce(bp);
}

static void place(void *bp, size_t asize) {

    //the size of the block found is bp
    //asize is the size required
    size_t csize = GET_SIZE(HDRP(bp));
    printf("csize : %ld, asize: %ld\n",csize, asize);
    size_t change_size = csize - asize;
    //printf("change_size: %ld\n",change_size);
    /*
    if the size of the block found is say 72 but asize only needs 32
    then 72-32 = 40 >= 8 + 16 thus it will set the remaining tail
    40 blocks to open memory.

    If say bp was only 40 then 40-32 would still be greater than 0 but not the
    24 required to make a block.  it isn't even worth it to free the
    remaining 8 Words because it couldn't fit a header, footer and some data inside so
    if a function tried to look for it it could find a block of 8 but nothing could fit
    inside so instead its left as leftover garbage.  This is a place of failure for
    stack utilization


    TODO: make this more efficient
    */
    if((change_size) >= (DSIZE + OVERHEAD)) {
      printf("not the 56\n");
        PUT(HDRP(bp), PACK(asize,1));
        PUT(FTRP(bp), PACK(asize,1));

        remove_node(csize, HDRP(bp));
//REMOVE NODE BP FROM ROOT

        bp = NEXT_BLKP(bp);
        //we could just free it for now, but optimize later to not coalesce
        //since coalesce in this context is pointless. TODO: more efficient
        PUT(HDRP(bp), PACK((change_size), 0));
        PUT(FTRP(bp), PACK((change_size), 0));

        //this is to open up first 8 bytes so that free block points to null
        PUT(bp,0);

        //mm_free(bp);
        //void *ptr = bp;
        //ptr = coalesce(ptr);
        //int size = GET_SIZE(HDRP(ptr));
        printf("PLACE: Size of free'd block: %d\n", change_size);
        // PUT(HDRP(ptr), PACK(size,0));
        // PUT(FTRP(ptr), PACK(size,0));
        // size = GET_SIZE(HDRP(ptr));
        add_node_to_root(change_size, bp);
        printf("PLACE: mm_check \n");
        mm_check(debug);
        //replaced by free(bp);
    } else {
      printf("THIS GOES FOR the 48?\n");
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
        remove_node(csize, HDRP(bp));
    }
}

static void *find_fit(size_t asize) {
  /*
    // #ifdef NEXT_FIT
    // // next fit search
    // char *oldrover = rover;
    //
    // for( ; GET_SIZE(HDRP(rover)) > 0; rover = NEXT_BLKP(rover)) {
    //     if(!GET_ALLOC(HDRP(rover)) && (asize <= GET_SIZE(HDRP(rover)))) {
    //         return rover;
    //     }
    // }
    //
    // for(rover = heap_listp; rover < oldrover; rover = NEXT_BLKP(rover)) {
    //     if(!GET_ALLOC(HDRP(rover)) && (asize <= GET_SIZE(HDRP(rover)))) {
    //         return rover;
    //     }
    // }
    //
    // return NULL;
    */
    /*Segregated Class List */
      void *p;

      // static int is_root_list_empty(void *root) {
      //   void *a = next_node(root);
      //   //char *a = ((char *)(GET(NEXT_NODE(root))));
      //   if(a == NULL) {
      //     return 1;
      //   } else {
      //     return 0;
      //   }
      // }

    size_t size_class = get_size_class(asize);
    //printf("segregate class list getsize_class size_class: %ld, size: %ld\n",size_class, asize);
    p = (void *)(get_root(size_class));
    for(; size_class < num_of_size_class_p;) {
        //if there exists a next node in the linked list at a given root
        if(p != NULL) {
            while(next_node(p) != NULL) {
                p = (void *)(NEXT_NODE(p));
                if(GET_SIZE(HDRP(p)) >= asize) {
                    return p;
                }
            }
        }
        size_class++;
        p = (void*)(get_root(size_class));
    }

    // while((is_root_list_empty(p)) && (size_class < num_of_size_class_p)) {
    //   size_class = size_class + 1;
    //   p = (void *)(get_root(size_class));
    // }


    if(is_root_list_empty(p)) {
      printf("class %d empty so we need to go on\n",size_class);
    } else {
      printf("nah\n");
    }
    printf("P: %p, size_class: %ld, asize: %ld\n",p,size_class,asize);
    //if there is no list with a size big enough for the block
    if(size_class >= num_of_size_class_p) {
      printf("OFF THE DEEPEND?---------------------------------------------\n");
      return NULL;
    } else {
      //as of right now p either equals a pointer to a root's first variable or its at the end
      // and has already returned null so, we need to get the root's first pointer variable address,
      //the spot where the free block is and pass that pointer on for malloc.
      return ((void *)(GET(p)));
    }


    // #else
    /* first fit search */
    // void *bp;
    //
    // for(int i = 0; i < num_of_size_class_p; i++) {
    //     bp = heap_listp + (i * OVERHEAD * 2) + OVERHEAD + WSIZE;
    //         //list begin  offset by each ptr   prologue   begin header
    //     //bp is now pointed at scp_1 at where it is right in front of the value pointer.
    //     void *next;
    //     next = NEXT_NODE(bp);
    //     while(next != 0) {//if the block isn't null
    //         int b_size = GET_SIZE(HDRP(next));
    //         int b_aloc = GET_ALLOC(HDRP(next));
    //         if(!b_aloc && b_size >= asize) {
    //             return next;
    //         }
    //         next = NEXT_NODE(next);
    //     }
    // /* if it reaches this bit of the loop that means that it couldn't find a block of that size class
    // so it will now begin to look in the next class */
    // }
    //
    //
    //
    //
    //
    //
    //
    // for(bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
    //     if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
    //         return bp;
    //     }
    // }
    //
    // return NULL; /* no fit */
    // #endif
}

static void *coalesce(void *bp) {

    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    size_t next_size = GET_SIZE(HDRP(NEXT_BLKP(bp)));
    size_t prev_size = GET_SIZE(HDRP(PREV_BLKP(bp)));

    if(prev_alloc && next_alloc) {
        return bp;
    } else if(prev_alloc && !next_alloc) {
        size += next_size;
        remove_node(next_size,NEXT_BLKP(bp));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    } else if(!prev_alloc && next_alloc) {
      remove_node(prev_size,PREV_BLKP(bp));
        size += prev_size;
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    } else {
        size += next_size + prev_size;
        remove_node(next_size,NEXT_BLKP(bp));
        remove_node(prev_size,PREV_BLKP(bp));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    #ifdef NEXT_FIT
    /* make sure we aren't pointing into a free block that we just coalesced */
    if((rover > (char *)(bp)) && (rover < NEXT_BLKP(bp))) {
        rover = bp;
    }
    #endif

    return bp;
}

static void printblock(void *bp) {

    size_t hsize, halloc, fsize, falloc;

    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));

    if(hsize == 0) {
        printf("%p: EOL\n\n", bp);
        return;
    }

    printf("%p: header: [%ld:%c] footer: [%ld:%c]\n", bp, hsize,
        (halloc ? 'a' : 'f'), fsize, (falloc ? 'a' : 'f'));
}

static void checkblock(void *bp) {
    if((size_t)bp % DSIZE) {
        printf("Erorr: %p is not doubleword aligned \n", bp);
    }
    if(GET(HDRP(bp)) != GET(FTRP(bp))) {
        printf("Error: header does not match footer!\n");
    }
}
