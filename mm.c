
    /* 
      Team name : A Team
      Members:    Parth Kanakiya  201401100@daiict.ac.in
                  Mihir Limbachia 201401456@daiict.ac.in

     * Simple, 32-bit and 64-bit clean allocator based on an Segregated free lists,
     * modified first fit, and boundary tag coalescing.
     * Here ten seperate segregated free list are defined which seprate free blocks according to their sizes into these lists.
     * However there is only one heap as per requirement of assignment.
     * Blocks are aligned to double-word boundaries.This
     * yields 8-byte aligned blocks on a 32-bit processor, and 16-byte aligned
     * blocks on a 64-bit processor.
     * This allocator uses the size of a pointer, e.g., sizeof(void *), to
     * define the size of a word.  This allocator also uses the standard
     * type uintptr_t to define unsigned integers that are the same size
     * as a pointer, i.e., sizeof(uintptr_t) == sizeof(void *).
     */

    #include <stdbool.h>
    #include <stdint.h>
    #include <stdio.h>
    #include <string.h>
    
    #include "memlib.h"
    #include "mm.h"

    /*********************************************************
     * NOTE TO STUDENTS: Before you do anything else, please
     * provide your team information in the following struct.
     ********************************************************/
    team_t team = {
        /* Team name */
        "A team",
            /* First member's full name */
        "Parth",
        /* First member's email address */
        "201401100@daiict.ac.in",
        /* Second member's full name (leave blank if none) */
        "Mihir",
        /* Second member's email address (leave blank if none) */
        "201401456@daiict.ac.in"
    };

    /* Basic constants and macros: */
    #define WSIZE       sizeof(void *)         /* word size (bytes) */
    #define DSIZE       (2 * WSIZE)            /* doubleword size (bytes) */
    #define CHUNKSIZE   (1<<12)      /* initial heap size (bytes) */

    #define MAX(x,y) ((x) > (y)?(x) :(y))
    #define true 1
    #define false 0
    /* Pack a size and allocated bit into a word */
    #define PACK(size, alloc) ((size) | (alloc))

    /* Read and write a word at address p */
    #define GET(p)          (*(uintptr_t *)(p))
    #define PUT(p,val)      (*(uintptr_t *)(p) = (val))

    /* Read the size and allocated fields from address p */
    #define GET_SIZE(p)     (GET(p) & ~(DSIZE - 1))
    #define GET_ALLOC(p)    (GET(p) & 0x1)


    /* Given block ptr bp, compute address of its header and footer */
    #define HDRP(bp)        ((char *)(bp) - WSIZE)
    #define FTRP(bp)        ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

    /* Given block ptr bp, compute address of next and previous blocks */
    #define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
    #define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))
    void* heaplistp = NULL;
    size_t no_of_lists = 10;
    void  **free_listp;

    /*Structure of free blocks: [header][next][prev]......[footer]
      Thus the bp points to the prevoius free block in the list         */

    //            get explicit free list previous and next blocks 
    #define LIST_NEXT_BLKP(bp) GET(bp)
    #define LIST_PREV_BLKP(bp) GET((char *)(bp)+WSIZE) //(char*)(bp) casting necessary for raw address manipulation (the bits of the address)

    //            set explicit free list previous and next blocks
    #define LIST_SET_NEXT_BLKP(bp, next) PUT(bp, next)
    #define LIST_SET_PREV_BLKP(bp, prev) PUT((char *)(bp)+WSIZE, prev) 

    /* Function prototypes for internal helper routines: */
    static void *coalesce(void *bp);
    static void *extend_heap(size_t words);
    static void *find_fit(size_t asize);
    void place(void *bp, size_t asize ,bool heapExtended);

    /* Function prototypes for heap consistency checker routines: */
    static void checkblock(void *bp);
    static void checkheap(bool verbose);
    static void printblock(void *bp); 

    /* function that are implemented  */
    int list_index(size_t size);
    void add (void *bp);
    void delete (void *bp);
    void *LIFO_coalesce(void *bp);


    /* 
     * Requires:
     *   None.
     *
     * Effects:
     *   Initialize the memory manager.  Returns 0 if the memory manager was
     *   successfully initialized and -1 otherwise.
         Initialises the listpinters to NULL
     */
    int mm_init(void)
    {
        if((free_listp=mem_sbrk(WSIZE*no_of_lists))==(void *)-1)     //since we have to use heap space as the space allocated for the freelistp so we call mm_sbrk function and return if there is an error
             return -1;


        if ((heaplistp = mem_sbrk(4*WSIZE)) == (void *)-1)
            return -1;
        PUT(heaplistp, 0);                         // alignment padding
        PUT(heaplistp + (1 * WSIZE), PACK(DSIZE, 1));   // prologue header
        PUT(heaplistp + (2 * WSIZE), PACK(DSIZE, 1));   // prologue footer
        PUT(heaplistp + (3 * WSIZE), PACK(0, 1));    // epilogue header
        heaplistp += DSIZE; //block pointer of first block

        int i;
        for (i = 0; i < no_of_lists; i++)
            free_listp[i] = NULL;

        return 0;
    }
    /* 
       Some  of the helper routines that need to be defined to use in malloc function are :
                     list_index
                     find_fit
                     add
                     delete
                     extend_heap
                     */
    /*
       list_index
       GET THE INDEX OF THE LIST THAT SATISFIES THE SIZE ACCORDING TO LIST CLASSIFICATION  */
    int list_index(size_t size) {
        if (size>16384)return 9;
        else if (size>8192)return 8;
        else if (size>4096)return 7;
        else if (size>2048)return 6;
        else if (size>1024)return 5;
        else if (size>512)return 4;
        else if (size>256)return 3;
        else if (size>128)return 2;
        else if (size>64)return 1;
        else return 0;
    }
    /* add
       add the free block pointer to appropriate segregated free list */
    void add (void *bp){
        int index = list_index(GET_SIZE(HDRP(bp)));
        LIST_SET_NEXT_BLKP(bp, free_listp[index]); 
        LIST_SET_PREV_BLKP(bp, NULL); 
        if (free_listp[index] != NULL) 
                LIST_SET_PREV_BLKP(free_listp[index], bp);    
        free_listp[index] = bp; 
        return; 
    }
    /*delete 
      Remove the allocated block pointer from its assigned segregated free list */
    void delete (void *bp){
        int index = list_index(GET_SIZE(HDRP(bp)));
        if (LIST_PREV_BLKP(bp) != NULL) 
            LIST_SET_NEXT_BLKP(LIST_PREV_BLKP(bp),LIST_NEXT_BLKP(bp));
        else free_listp[index] = LIST_NEXT_BLKP(bp);
        if (LIST_NEXT_BLKP(bp) != NULL) 
            LIST_SET_PREV_BLKP(LIST_NEXT_BLKP(bp), LIST_PREV_BLKP(bp));
        return;
    }
    /* 
     * Requires:
     *   None.
     *
     * Effects:
     *   Extend the heap with a free block and return that block's address.
     */
    void *extend_heap(size_t words)
    {
        char *bp;
        size_t size;
        /* Allocate an even number of words to maintain alignments */
        size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
        if ( (bp = mem_sbrk(size)) == (void *)-1 )
            return NULL;
        /* Initialize free block header/footer and the epilogue header */
        PUT(HDRP(bp), PACK(size, 0));                // free block header
        PUT(FTRP(bp), PACK(size, 0));                // free block footer
        PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));        // new epilogue header
        return bp;
    }
    /* 
    find_fit  
    finds the free block best suitable by waiting for suitable free block to occcur for twentieth time and each subsequent suitable block has less fragmentation beacuse of condition 
     diff <lowest    
     */
    void *find_fit(size_t asize) {
        int c= 0;
        int wait = 20; 
        size_t lowest= 9999999;
        void *best= NULL;
        int index = list_index(asize);
        int i;
        for (i = index; i < no_of_lists; i++) {        
            void *bp = free_listp[i]; 
            while (bp) { 
                size_t curr = GET_SIZE(HDRP(bp));
                if (!GET_ALLOC(HDRP(bp)) && (asize <= curr)) {
                    c++; 
                    size_t diff =curr-asize;
                    if (diff < lowest) {                              /* get the better occuring fit for 20 times*/
                        lowest = diff;
                        best = bp;
                    }
                    if (c > wait)
                        return best; 
                }
                bp  = LIST_NEXT_BLKP(bp);
            }
        }
        return best; 
    }
    /* It marks the block as allocated and splits the block if there is a case */
    void place(void* bp, size_t asize, bool heapExtended)
    {
        size_t bsize = GET_SIZE(HDRP(bp));
        if (heapExtended == true) {
            if (asize <= bsize-4*WSIZE) {                                    /* condition for spliting as the allocated size is less than the current block payload size*/
                PUT(HDRP(bp), PACK(asize, 1));
                PUT(FTRP(bp), PACK(asize, 1));
                size_t excess_size = bsize - asize;
                void *new_spliced = NEXT_BLKP(bp);
                PUT(HDRP(new_spliced), PACK(excess_size, 0));
                PUT(FTRP(new_spliced), PACK(excess_size, 0)); 
                add(new_spliced);
            }
            else {
                PUT(HDRP(bp), PACK(bsize, 1));
                PUT(FTRP(bp), PACK(bsize, 1));
            }
        } else { 
            if (asize <= bsize-4*WSIZE) {                                     /* condition for spliting as the allocated size is less than the current block payload size*/
                delete(bp);      
                PUT(HDRP(bp), PACK(asize, 1));
                PUT(FTRP(bp), PACK(asize, 1));     
                size_t excess_size = bsize - asize;
                void *new_spliced = NEXT_BLKP(bp);
                PUT(HDRP(new_spliced), PACK(excess_size, 0));
                PUT(FTRP(new_spliced), PACK(excess_size, 0)); 
                add(new_spliced);
            }
            else {
                PUT(HDRP(bp), PACK(bsize, 1));
                PUT(FTRP(bp), PACK(bsize, 1));
                delete(bp);
            }    
        }
    }
    /* 
     * Requires:
     *   None.
     *
     * Effects:
     *   Allocate a block with at least "size" bytes of payload, unless "size" is
     *   zero.  Returns the address of this block if the allocation was successful
     *   and NULL otherwise.
     */
    void *mm_malloc(size_t size)
    {
        size_t asize; /* adjusted block size */
        size_t extendsize; /* amount to extend heap if no fit */
        char * bp;

        /* Ignore spurious requests */
        if (size == 0)
            return NULL;
        /* Adjust block size to include overhead and alignment reqs. */
        if (size <= DSIZE)
            asize = 2*DSIZE;
        else  asize = DSIZE * ((size + (DSIZE) + (DSIZE-1))/ DSIZE);
     
        /* Search the free list for a fit */
        if ((bp = find_fit(asize)) != NULL) {
            place(bp, asize, false);
            return bp;
        }
        extendsize = MAX(asize, CHUNKSIZE);
        /* No fit found. Get more memory and place the block */
        if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
            return NULL;
        place(bp, asize, true);
        return bp;
    }
    /* LIFO_coalesce
       coalesces the block and takes care of the free blocks (that are used in coalescing) in their assigned segregated list 
       case 1 both prev and next block allocated
       case 2 prev block allocated next free
       case 3 next block allocated prev free
       case 4 both prev and next block free
    */
    void *LIFO_coalesce(void *bp) {
        size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
        size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
            if (prev_alloc && next_alloc) {
            add(bp);               //case 1
        } 
        if (prev_alloc && !next_alloc) {
            void *next = NEXT_BLKP(bp); // case 2
            delete(next);
            bp = coalesce(bp);
            add(bp); 
        }
        if (!prev_alloc && next_alloc) { // case 3
            void *prev = PREV_BLKP(bp);
            delete(prev);
            bp = coalesce(bp);
            add(bp);
        }
        if (!prev_alloc && !next_alloc) { //case 4
            void *prev = PREV_BLKP(bp);
            void *next = NEXT_BLKP(bp);
            delete(prev);
            delete(next);
            bp = coalesce(bp);
            add(bp);
        }
        return bp;
    }
    /* 
     * Requires:
     *   "bp" is either the address of an allocated block or NULL.
     *
     * Effects:
     *   Free a block and calls LIFO_coalesce as we need to take care of effect of coalescing in free list also
     */
    void mm_free(void *bp)
    {
        if(bp == NULL){
            return;
        }    
        size_t size = GET_SIZE(HDRP(bp));
        PUT(HDRP(bp), PACK(size,0));
        PUT(FTRP(bp), PACK(size,0));
        LIFO_coalesce(bp);
    }
    /*
     * The following routines are internal helper routines.
     */

    /*
     * Requires:
     *   "bp" is the address of a newly freed block.
     *
     * Effects:
     *   Perform boundary tag coalescing.  Returns the address of the coalesced
     *   block.
     */
    void *coalesce(void *bp)
    {
        size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
        size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
        size_t size = GET_SIZE(HDRP(bp));

        if (prev_alloc && next_alloc) {       /* Case 1 */
            return bp;
        }

        else if (prev_alloc && !next_alloc) { /* Case 2 */
            size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
            PUT(HDRP(bp), PACK(size, 0));
            PUT(FTRP(bp), PACK(size, 0));
            return (bp);
        }

        else if (!prev_alloc && next_alloc) { /* Case 3 */
            size += GET_SIZE(HDRP(PREV_BLKP(bp)));
            PUT(FTRP(bp), PACK(size, 0));
            PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
            return (PREV_BLKP(bp));
        }

        else {            /* Case 4 */
            size += GET_SIZE(HDRP(PREV_BLKP(bp)))  +
                GET_SIZE(FTRP(NEXT_BLKP(bp)))  ;
            PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
            PUT(FTRP(NEXT_BLKP(bp)), PACK(size,0));
            return (PREV_BLKP(bp));
        }
    }
    /*
     * Requires:
     *   "ptr" is either the address of an allocated block or NULL.
     *
     * Effects:
     *   Reallocates the block "ptr" to a block with at least "size" bytes of
     *   payload, unless "size" is zero.  If "size" is zero, frees the block
     *   "ptr" and returns NULL.If the block "ptr" is already a block with at
     *   least "size" bytes of payload, then "ptr" may optionally be returned.
     *   If the block can be coalesced with next free block and the reallocation
         request can be satisfied than no new allocation is required.
         Otherwise, a new block is allocated and the contents of the old block
     *   "ptr" are copied to that new block.  Returns the address of this new
     *   block if the allocation was successful and NULL otherwise.
     */
    void *mm_realloc(void *ptr, size_t size)
    {
        if (size == 0){
            mm_free(ptr);
            return NULL;
        }
        size_t curr = GET_SIZE(HDRP(ptr));
        if (size < curr-2*WSIZE) {                       // if size is less than the old block's payload size than we return the current block as it fits  
            return ptr;
        }
        void *next = NEXT_BLKP(ptr);
        int next_alloc = GET_ALLOC(HDRP(next));
        size_t coalesce_size=(GET_SIZE(HDRP(next)) + GET_SIZE(HDRP(ptr)));
        if (!next_alloc && size <= coalesce_size-2*WSIZE){  // If the block can be coalesced with next free block and the reallocation request can be satisfied than no new allocation is required
            delete(next);
            PUT(HDRP(ptr), PACK(coalesce_size, 1));
            PUT(FTRP(ptr), PACK(coalesce_size, 1));
            return ptr;
        }
        if (ptr == NULL)return (mm_malloc(size));          // If the ptr is null than we have to reallocate to a new block and so malloc is called
        void *oldptr = ptr;
        void *newptr;
        size_t copySize;
        newptr = mm_malloc(size);                          
        if (newptr == NULL)
            return NULL;
        copySize = GET_SIZE(HDRP(oldptr));
        if (size < copySize)                                // if the blocksize is greater than size that has to be allocated we want it to place the allocated size in the block header so we do this
            copySize = size;
        memcpy(newptr, oldptr, copySize);
        mm_free(oldptr);
        return newptr;
    }
    /*
     * checkheap
     * Check the consistency of the memory heap
     * Return nonzero if the heap is consistant.
   
     */
     
    void checkheap(bool verbose){
        int i;
        void *bp;  
        bp=heaplistp;
        
        for(i = 0; i < no_of_lists; i++) {
            bp = free_listp[i];         
            while (bp) {            

                      //we should check if there is a allocated block in free list and print if there is an error
                if (GET_ALLOC(HDRP(bp)) == 1 || GET_ALLOC(FTRP(bp)) == 1){
                        printf("Encountered an allocated block in free list");
                        return;
                }                  
                bp  = LIST_NEXT_BLKP(bp);
            }
        }
        
            if (verbose)
            printf("Heap (%p):\n", heaplistp);


            if (GET_SIZE(HDRP(heaplistp)) != DSIZE ||!GET_ALLOC(HDRP(heaplistp)))
                        printf("Bad prologue header\n");                             // check if there is an error in proogue header 
            checkblock(heaplistp);
            for (bp = heaplistp; GET_SIZE(HDRP(bp)) > 0; bp = (void *)NEXT_BLKP(bp)) {
                        if (verbose)
                        printblock(bp);
                        checkblock(bp);
                void *next=NEXT_BLKP(bp);
                void *prev=PREV_BLKP(bp);
                      if(next !=NULL && !GET_ALLOC(next) && !GET_ALLOC(bp) && prev !=NULL && !GET_ALLOC(prev) && !GET_ALLOC(bp))
                     printf("Contigious %x free block escaped coalescing\n",next); // check if next block in heap space was free and if it is we have not performed proper coalescing 
                      

                        if(!GET_ALLOC(bp)){
                                         int flag=0;
                                         for(i = 0; i < no_of_lists; i++) {     
                                                void *find;
                                                find = free_listp[i];         
                                                    while (find) {          
                                                                // checking if free block is in the free list          
                                                  
                                                      if(*(int *)find==*(int *)bp){
                                                                flag=1;
                                                                break;
                                                      }
                                                       if(flag==1)break; 
                                                      find  = LIST_NEXT_BLKP(find);
                        
                }                              
            }

                if(flag==0)printf("A free Block not in the Free list\n");                // if not printing this
        
        } 

        if(GET_ALLOC(HDRP(bp)) == 1 && GET_ALLOC(HDRP(NEXT_BLKP(bp))) == 1)
        {
            if( HDRP(NEXT_BLKP(bp)) != FTRP(bp) + WSIZE )                               // checking if the header  of next block is at word size from footer of current block
            {
                printf("Allocated blocks overlap\n");                                     // if not we print this
                return;
            }
        }
    
}
                    if (verbose)printblock(bp);
            if (GET_SIZE(HDRP(bp)) != 0 || !GET_ALLOC(HDRP(bp)))                        
            printf("Bad epilogue header\n");                                            // check if there is an error in proogue header 
    
        printf("end");
    }
    /*
     * Requires:
     *   "bp" is the address of a block.
     *
     * Effects:
     *   Print the block "bp".
     */
     
    static void
    printblock(void *bp) 
    {
        bool halloc, falloc;
        size_t hsize, fsize;

        checkheap(false);
        hsize = GET_SIZE(HDRP(bp));
        halloc = GET_ALLOC(HDRP(bp));  
        fsize = GET_SIZE(FTRP(bp));
        falloc = GET_ALLOC(FTRP(bp));  

        if (hsize == 0) {
            printf("%p: end of heap\n", bp);
            return;
        }

        printf("%p: header: [%zu:%c] footer: [%zu:%c]\n", bp, 
            hsize, (halloc ? 'a' : 'f'), 
            fsize, (falloc ? 'a' : 'f'));
    }

    /*
     * Requires:
     *   "bp" is the address of a block.
     *
     * Effects:
     *   Perform a minimal check on the block "bp".
     */
    
    static void
    checkblock(void *bp) 
    {

        if ((uintptr_t)bp % DSIZE)
            printf("Error: %p is not doubleword aligned\n", bp);
        if (GET(HDRP(bp)) != GET(FTRP(bp)))
            printf("Error: header does not match footer\n");
    }
    
    /*
     * The last lines of this file configures the behavior of the "Tab" key in
     * emacs.  Emacs has a rudimentary understanding of C syntax and style.  In
     * particular, depressing the "Tab" key once at the start of a new line will
     * insert as many tabs and/or spaces as are needed for proper indentation.
     */

    /* Local Variables: */
    /* mode: c */
    /* c-default-style: "bsd" */
    /* c-basic-offset: 8 */
    /* c-continued-statement-offset: 4 */
    /* indent-tabs-mode: t */
    /* End: */
