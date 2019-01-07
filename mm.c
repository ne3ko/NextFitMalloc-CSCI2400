/* 
 * mm-implicit.c -  Simple allocator based on implicit free lists, 
 *                  first fit placement, and boundary tag coalescing. 
 *
 * Each block has header and footer of the form:
 * 
 *      31                     3  2  1  0 
 *      -----------------------------------
 *     | s  s  s  s  ... s  s  s  0  0  a/f
 *      ----------------------------------- 
 * 
 * where s are the meaningful size bits and a/f is set 
 * iff the block is allocated. The list has the following form:
 *
 * begin                                                          end
 * heap                                                           heap  
 *  -----------------------------------------------------------------   
 * |  pad   | hdr(8:a) | ftr(8:a) | zero or more usr blks | hdr(8:a) |
 *  -----------------------------------------------------------------
 *          |       prologue      |                       | epilogue |
 *          |         block       |                       | block    |
 *
 * The allocated prologue and epilogue blocks are overhead that
 * eliminate edge conditions during coalescing.
 */
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <memory.h>
#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
  /* Team name */
  "Team Alexander",
  /* First member's full name */
  "Nikolai Alexander",
  /* First member's email address */
  "nial3328@colorado.edu",
  /* Second member's full name (leave blank if none) */
  "",
  /* Second member's email address (leave blank if none) */
  ""
};

/////////////////////////////////////////////////////////////////////////////
// Constants and macros
//
// These correspond to the material in Figure 9.43 of the text
// The macros have been turned into C++ inline functions to
// make debugging code easier.
//
/////////////////////////////////////////////////////////////////////////////
#define WSIZE       4       /* word size (bytes) */  
#define DSIZE       8       /* doubleword size (bytes) */
#define CHUNKSIZE  (1<<12)  /* initial heap size (bytes) */
#define OVERHEAD    8       /* overhead of header and footer (bytes) */

static inline int MAX(int x, int y) {
  return x > y ? x : y;
}

//
// Pack a size and allocated bit into a word
// We mask of the "alloc" field to insure only
// the lower bit is used
//
static inline uint32_t PACK(uint32_t size, int alloc) {
  return ((size) | (alloc & 0x1));
}

//
// Read and write a word at address p
//
static inline uint32_t GET(void *p) { return  *(uint32_t *)p; }
static inline void PUT( void *p, uint32_t val)
{
  *((uint32_t *)p) = val;
}

//
// Read the size and allocated fields from address p
//
static inline uint32_t GET_SIZE( void *p )  { 
  return GET(p) & ~0x7;
}

static inline int GET_ALLOC( void *p  ) {
  return GET(p) & 0x1;
}

//
// Given block ptr bp, compute address of its header and footer
//
static inline void *HDRP(void *bp) {

  return ( (char *)bp) - WSIZE;
}
static inline void *FTRP(void *bp) {
  return ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE);
}

//
// Given block ptr bp, compute address of next and previous blocks
//
static inline void *NEXT_BLKP(void *bp) {
  return  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)));
}

static inline void* PREV_BLKP(void *bp){
  return  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)));
}

/////////////////////////////////////////////////////////////////////////////
//
// Global Variables
//

static char *heap_listp;  /* pointer to first block */  
static char *next_fit;	  // Global placeholder for nextfit search

//
// function prototypes for internal helper routines
//
static void *extend_heap(uint32_t words);
static void place(void *bp, uint32_t asize);
static void *find_fit(uint32_t asize);
static void *coalesce(void *bp);
static void printblock(void *bp); 
static void checkblock(void *bp);

//
// mm_init - Initialize the memory manager 
//
// Implicit Free list code from Computer Systems: A Programmer's Perspective,
// page 858.
int mm_init(void) 
{
  // Creates a heap size 16 bytes to fit four words
  // heap_listp contains address of starting point
  if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *) -1){
    return -1;
  }

  // First word - Allignment padding (Free)
  PUT(heap_listp, 0);
  // Prologue header allocation
  PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1));
  // Prologue footer allocation
  PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1));
  // Epilogue Header
  PUT(heap_listp + (3 * WSIZE), PACK(0,1));

  // Move between header and footer
  heap_listp += (2*WSIZE);
  // Move next_fit spot to beginning of heap
  next_fit = heap_listp;

  // Extend the size of the heap
  if (extend_heap(CHUNKSIZE/WSIZE) == NULL){
    return -1;
  }

  return 0;
}


//
// extend_heap - Extend heap with free block and return its block pointer
//
// Implicit Free list code from Computer Systems: A Programmer's Perspective,
// page 858.
static void *extend_heap(uint32_t words) 
{
  char *bp;
  size_t size;

  // Make sure the number of words is always even to maintain alignment
  size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;


  // If there is space, extend the heap by 'size'
  if ((long)(bp = mem_sbrk(size)) == -1){
    return NULL;
  }

  // Deallocate header and footer on block
  PUT(HDRP(bp), PACK(size, 0));
  PUT(FTRP(bp), PACK(size,0));
  // Allocate new epiloge to avoid edge conditions
  PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1));

  // Merge blocks into one using coalesce function
  return coalesce(bp);
}


//
// Practice problem 9.8
//
// find_fit - Find a fit for a block with asize bytes 
//
// Implicit Free list code from Computer Systems: A Programmer's Perspective,
// page 884.
static void *find_fit(uint32_t asize)
{
  // Assigns beginning of the search to the next_fit pointer
  char *bp = next_fit;

  // Search from next_fit to the end of the heap
  for (next_fit = bp; GET_SIZE(HDRP(next_fit)) > 0; next_fit = NEXT_BLKP(next_fit)){
    if(!GET_ALLOC(HDRP(next_fit)) && (asize <= GET_SIZE(HDRP(next_fit)))){
      // If a fit is found, return the address the of block pointer
      return next_fit;
    }
  }

  // If no fit is found by the end of the heap, start the search from the
  // beginning of the heap to the original next_fit location
  for (next_fit = heap_listp; next_fit < bp; next_fit = NEXT_BLKP(next_fit)){
    if(!GET_ALLOC(HDRP(next_fit)) && (asize <= GET_SIZE(HDRP(next_fit)))){
      return next_fit;
    }
  }

  // If no fit is found, return NULL
  return NULL;
}

// 
// mm_free - Free a block 
//
// Implicit Free list code from Computer Systems: A Programmer's Perspective,
// page 860.
void mm_free(void *bp)
{
  // Get the block size
  size_t size = GET_SIZE((HDRP(bp)));

  // Deallocate header and footer
  PUT(HDRP(bp), PACK(size, 0));
  PUT(FTRP(bp), PACK(size, 0));
  // Combine with surrounding free blocks
  coalesce(bp);
}

//
// coalesce - boundary tag coalescing. Return ptr to coalesced block
//
// Implicit Free list code from Computer Systems: A Programmer's Perspective,
// page 860.
static void *coalesce(void *bp) 
{
  // Find footers and headers of previous and next blocks respectively
  size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
  size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
  size_t size = GET_SIZE(HDRP(bp));

  // Case 1 - If both the previous and next blocks are allocated
  if (prev_alloc && next_alloc){
  	// Return bp - can't extend block size
    return bp;
  }
  // Case 2 - If the next block is free
  else if (prev_alloc && !next_alloc){
  	// Increase the size of the block to fit the next block
    size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
    // Place header and footer on the new concatenated block
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
  }
  // Case 3 - If the previous block is free
  else if (!prev_alloc && next_alloc){
  	// Increase size of block to fit previous block
    size += GET_SIZE(HDRP(PREV_BLKP(bp)));
    // Place header and footer of concatenated block with new block size
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    // Set the starting address of the block pointer to the previous block location
    bp = PREV_BLKP(bp);
  }
  // Case 4 - If both blocks are free
  else{
  	// Increase the size of the block to fit both the previous and next blocks
    size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
    // Place headers and footers at new concatenated blocks
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
    PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
    // Set the starting address of the block pointer to the previous block's starting address
    bp = PREV_BLKP(bp);
  }

  // Make sure our next_fit pointer isn't sitting in the middle of coalesced block
  if ((next_fit >= (char *)bp) && (next_fit < (char *)NEXT_BLKP(bp))){
  	// If it is, just set it to the beginning of the coalesced block
    next_fit = bp;
  }

  // return new block
  return bp;
}

//
// mm_malloc - Allocate a block with at least size bytes of payload 
//
// Implicit Free list code from Computer Systems: A Programmer's Perspective,
// page 860.
void *mm_malloc(uint32_t size) 
{
  size_t asize;
  size_t extendsize;
  char *bp;

  // Ignore spurious requests
  if (size == 0){
    return NULL;
  }

  // Extend size to fit header and footer & satisfy double word alignment
  if (size <= DSIZE){
    asize = 2*DSIZE;
  }
  else {
    asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
  }

  // Search for a block that fits this request - Next Fit
  if ((bp = find_fit(asize)) != NULL){
    place(bp, asize);
    return bp;
  }

  // If there is no fit, it extends the heap with a new free block
  extendsize = MAX(asize, CHUNKSIZE);
  if ((bp = extend_heap(extendsize/WSIZE)) == NULL){
  	// If we can't extend the heap any further, return NULL
    return NULL;
  }
  // Places the block in the new set of free blocks
  place(bp, asize);
  return bp;
} 

//
//
// Practice problem 9.9
//
// place - Place block of asize bytes at start of free block bp 
//         and split if remainder would be at least minimum block size
//
// Implicit Free list code from Computer Systems: A Programmer's Perspective,
// page 884.
static void place(void *bp, uint32_t asize)
{
  size_t csize = GET_SIZE(HDRP(bp));


  // If the remainder of the block is greater than or equal to 2 words
  if((csize - asize) >= (2*DSIZE)){
  	// Allocate needed block size
    PUT(HDRP(bp), PACK(asize, 1));
    PUT(FTRP(bp), PACK(asize, 1));
    // Split the block and deallocate the remainder
    bp = NEXT_BLKP(bp);
    PUT(HDRP(bp), PACK(csize - asize, 0));
    PUT(FTRP(bp), PACK(csize - asize, 0));
  }
  // If the remainder of the block is less than two words
  else{
  	// Allocate the entire block
    PUT(HDRP(bp), PACK(csize, 1));
    PUT(FTRP(bp), PACK(csize, 1));
  }

  // If next_fit is pointed at the new allocated block, move it to the next block
  if (next_fit == (char *)bp){
  	next_fit = NEXT_BLKP(bp);
  }
}


//
// mm_realloc -- implemented for you
//
void *mm_realloc(void *ptr, uint32_t size)
{
  void *newp;
  uint32_t copySize;

  newp = mm_malloc(size);
  if (newp == NULL) {
    printf("ERROR: mm_malloc failed in mm_realloc\n");
    exit(1);
  }
  copySize = GET_SIZE(HDRP(ptr));
  if (size < copySize) {
    copySize = size;
  }
  memcpy(newp, ptr, copySize);
  mm_free(ptr);
  return newp;
}

//
// mm_checkheap - Check the heap for consistency 
//
void mm_checkheap(int verbose) 
{
  //
  // This provided implementation assumes you're using the structure
  // of the sample solution in the text. If not, omit this code
  // and provide your own mm_checkheap
  //
  void *bp = heap_listp;
  
  if (verbose) {
    printf("Heap (%p):\n", heap_listp);
  }

  if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp))) {
	printf("Bad prologue header\n");
  }
  checkblock(heap_listp);

  for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
    if (verbose)  {
      printblock(bp);
    }
    checkblock(bp);
  }
     
  if (verbose) {
    printblock(bp);
  }

  if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp)))) {
    printf("Bad epilogue header\n");
  }
}

static void printblock(void *bp) 
{
  uint32_t hsize, halloc, fsize, falloc;

  hsize = GET_SIZE(HDRP(bp));
  halloc = GET_ALLOC(HDRP(bp));  
  fsize = GET_SIZE(FTRP(bp));
  falloc = GET_ALLOC(FTRP(bp));  
    
  if (hsize == 0) {
    printf("%p: EOL\n", bp);
    return;
  }

  printf("%p: header: [%d:%c] footer: [%d:%c]\n",
	 bp, 
	 (int) hsize, (halloc ? 'a' : 'f'), 
	 (int) fsize, (falloc ? 'a' : 'f')); 
}

static void checkblock(void *bp) 
{
  if ((uintptr_t)bp % 8) {
    printf("Error: %p is not doubleword aligned\n", bp);
  }
  if (GET(HDRP(bp)) != GET(FTRP(bp))) {
    printf("Error: header does not match footer\n");
  }
}

