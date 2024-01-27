/** Page size in bytes. */
const PAGE_SIZE: usize = 4096;

/** Cache size in bytes. */
const CACHE_SIZE: usize = PAGE_SIZE;
/** Line size in bytes. */
const LINE_SIZE: usize = 64;
/** Associativity of each set. (lines per set) */
const ASSOCIATIVITY: usize = 8;

/** Number of cache lines in the entire cache. */
const NCACHE_LINES: usize = CACHE_SIZE / LINE_SIZE;
/** Number of sets in the entire cache. */
const NSETS: usize = NCACHE_LINES / ASSOCIATIVITY;

/** Mask for the used bit. */
const USED: u64 = 0b1;
/** Mask for the dirty bit. */
const DIRTY: u64 = 0b10;

/** Number of bits used for the byte id. */
const NBYTEID_BITS: u64 = log2_power_of_two(LINE_SIZE);
/** Number of bits used for the set id. */
const NSETID_BITS: u64 = log2_power_of_two(NSETS);

/** Number of bits used for flags. */
const NFLAG_BITS: u64 = 2;

/** Mask for the byte id. */
const BYTEID_MASK: usize = (u64::MAX >> (64 - NBYTEID_BITS)) as usize;
/** Mask for the set id. */
const SETID_MASK: usize = (u64::MAX >> (64 - NSETID_BITS)) as usize;

/** Constant function to calculate the log 2 of a power of two. */
const fn log2_power_of_two(n: usize) -> u64 {
    63 - n.leading_zeros() as u64
}

/**
CPU 8-way set associative LRU cache for 64-bit address.

We break down the address thus:
    55 tag bits | 3 set id bits | 6 byte id bits

We need two flag bits and 55 tag bits in our metadata. Each set needs
8 cells for the queue, each of which has at least 3 bits (for the set id)
(24 bits in total). This means we want 64 line-metadata entries and 8
set-metadata entries.

Each set metadatum is just an LRU queue.
Each cache line metadatum is:
    7 padding bits | 55 tag bits | 1 dirty bit | 1 used bit

*/
pub struct Cache {
    cache: [u8; CACHE_SIZE],
    // Note that lruqueues must be changed manually if nsets changes. Must have
    // at least nsets * nsetid_bits bits in total. With the current nsets of 8
    // and nsetid_bits of 3, the optimal implementation is as a 32-bit int.
    lruqueues: [u32; NSETS],
    metadata: [u64; NCACHE_LINES],
}

/**
 * Gets a full cache line at addr from memory.
 */
pub fn from_mem(_addr: u64) -> [u8; LINE_SIZE] {
    panic!()
}

/**
 * Writes the bytes in the given slice to the memory at addr.
 */
pub fn write_mem(_addr: u64, _bytes: &[u8]) {
    panic!()
}

impl Cache {
    /**
     * Creates a new, zeroed out cache.
     */
    pub fn new() -> Cache {
        Cache { cache: [0; CACHE_SIZE], lruqueues: [u32::MAX; NSETS], metadata: [0; NCACHE_LINES] }
    }

    /**
     * Flushes the cache, writing all changes back to memory.
     */
    pub fn flush(&mut self) {
        // We don't need to zero the set metadata or the cache itself.
        for line in 0..self.metadata.len() {
            let meta = self.metadata[line];
            if meta & USED == 1 && meta & DIRTY == 0 {
                let addr = ((meta >> NFLAG_BITS << NFLAG_BITS + NSETID_BITS) | (line >> ASSOCIATIVITY) as u64) << NBYTEID_BITS;
                let data = &self.cache[LINE_SIZE * line .. LINE_SIZE * (line + 1)];
                write_mem(addr, data)
            }
            self.metadata[line] = 0
        }
    }

    /**
     * Reads the byte at addr, returning it.
     */
    pub fn read(&mut self, addr: u64) -> u8 {
        // Break down the address
        let byte_id = addr as usize & BYTEID_MASK;
        let shifted = addr as usize >> NBYTEID_BITS;
        let set_id  = shifted & SETID_MASK;
        let tag = (shifted >> NSETID_BITS) as u64;

        // Search through set
        for id_in_set in 0..ASSOCIATIVITY {
            let line = set_id * ASSOCIATIVITY + id_in_set;

            let meta = self.metadata[line];
            // If unused, no byte here
            if meta & USED == 0 { continue }

            // If tag correct, return the result
            if tag == meta >> NFLAG_BITS {
                // Upcycle the index in set to MRU
                self.upcycle(set_id, id_in_set);

                return self.cache[line * LINE_SIZE + byte_id]
            }
        }

        // Evict the LRU line from the set and save the spot
        let new_id_in_set: usize = self.evict(set_id) as usize;
        let line = set_id * ASSOCIATIVITY + new_id_in_set;

        // Upcycle the new id in set to MRU
        self.upcycle(set_id, new_id_in_set);

        // Read in the cache line from memory
        let memarr: [u8; LINE_SIZE] = from_mem((addr >> NBYTEID_BITS) << NBYTEID_BITS);
        for i in 0..memarr.len() {
            self.cache[line * LINE_SIZE + i] = memarr[i]
        }

        // Mark the line used (but not dirty)
        self.metadata[line] = ((self.metadata[line] >> NFLAG_BITS) << NFLAG_BITS) | USED;

        // Return the requested byte
        self.cache[line * LINE_SIZE + byte_id]
    }

    /**
     * Writes byte to addr.
    */
    pub fn write(&mut self, addr: u64, byte: u8) {
        // Break down the address
        let byte_id = addr as usize & BYTEID_MASK;
        let shifted = addr as usize >> NBYTEID_BITS;
        let set_id  = shifted & SETID_MASK;
        let tag = (shifted >> NSETID_BITS) as u64;

        // Search through set
        for id_in_set in 0..ASSOCIATIVITY {
            let line = set_id * ASSOCIATIVITY + id_in_set;
        
            let meta = self.metadata[line];
            // If unused, no byte here
            if meta & USED == 0 { continue }

            // If tag correct, write the byte
            if tag == meta >> NFLAG_BITS {
                self.cache[line * LINE_SIZE + byte_id] = byte;

                // Mark the metadata dirty
                self.metadata[line] |= DIRTY;
                
                // Upcycle the index in set to MRU
                return self.upcycle(set_id, id_in_set)
            }
        }

        // Evict the LRU line from the set and save the spot
        let new_id_in_set: usize = self.evict(set_id) as usize;
        let line = set_id * ASSOCIATIVITY + new_id_in_set;

        // Upcycle the new id in set to MRU
        self.upcycle(set_id, new_id_in_set);
        
        // Read in the cache line from memory
        let mut memarr: [u8; LINE_SIZE] = from_mem((addr >> NBYTEID_BITS) << NBYTEID_BITS);

        // Write the byte
        memarr[byte_id] = byte;
        for i in 0..memarr.len() {
            self.cache[line * LINE_SIZE + i] = memarr[i]
        }
    
        // Flag the line metadata as used and dirty
        self.metadata[line] = self.metadata[line] | USED | DIRTY;
    }

    /**
     * At set set_id, cycles cache line id_in_set to be the MRU line.
     */
    fn upcycle(&mut self, set_id: usize, id_in_set: usize) {
        // IMPLEMENTATION DETAIL: MRU should be leftmost, LRU should be rightmost
        let queue = self.lruqueues[id_in_set];
        let mut unseen = queue;
        let mut seen: u32 = 0;
        for i in 0..ASSOCIATIVITY {
            let id_in_set_i = unseen & 0b1111 as u32;
            unseen >>= 4;
            if id_in_set_i == 0b1111 {
                return self.lruqueues[id_in_set] = (queue << 4) | set_id as u32
            } else if id_in_set_i == id_in_set as u32 {
                return self.lruqueues[id_in_set] = (((unseen << 4 * i) | seen) << 4) | id_in_set_i
            }
            seen <<= 4;
            seen |= id_in_set_i;
        }
    }

    /**
     * Returns an empty cache line to be overwritten, whether because there is
     * already an empty cache line or because of evicting the MRU line.
     */
    fn evict(&mut self, set_id: usize) -> usize {
        for id_in_set in 0..ASSOCIATIVITY {
            let meta = self.metadata[set_id * ASSOCIATIVITY + id_in_set];
            if meta & USED == 0 { return id_in_set }
        }
        // IMPLEMENTATION-SPECIFIC QUEUE DETAIL -- the lru is the leftmost 4 bits
        let lru = (self.lruqueues[set_id] >> 28) as usize;
    
        let line = set_id * ASSOCIATIVITY + lru;
        let meta = self.metadata[line];
    
        // Perform writeback
        if meta & DIRTY == 1 {
            let addr = ((meta >> NFLAG_BITS << NFLAG_BITS + NSETID_BITS) | set_id as u64) << NBYTEID_BITS;
            let data = &self.cache[LINE_SIZE * line .. LINE_SIZE * (line + 1)];
            write_mem(addr, data)
        }

        // Zero out flag bits
        self.metadata[line] = self.metadata[line] >> NFLAG_BITS << NFLAG_BITS;
        lru
    }

}