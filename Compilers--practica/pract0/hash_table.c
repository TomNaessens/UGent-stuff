#include "hash_table.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>


/**** bucket creation, initialization, destruction, manipulation ****/

inline static void ht_init_bucket(t_bucket *b, t_key key, t_value value,
                                  t_bucket *next) {
    b->key = key;
    b->value = value;
    b->next = next;
}

inline static t_bucket *ht_create_bucket(t_hash_table *h, t_key key,
                                         t_value value, t_bucket *next) {
    t_bucket *b;
    b = (t_bucket *)malloc(sizeof(t_bucket));
    ht_init_bucket(b, key, value, next);
    h->num_keys++;
    return b;
}

inline static void ht_delete_bucket(t_hash_table *h, t_bucket *b) {
    free(b);
    h->num_keys--;
}

inline static t_bucket *ht_find_bucket(const t_hash_table *h, t_key key,
                                       int hash) {
    t_bucket *b;

    for (b = h->bucket_ptrs[hash]; b != NULL; b = b->next)
        if (b->key == key)
            return b;

    return NULL;
}


/**** hash function ****/

#define HT_HASH(I, S) ((((I) >> 8) ^ (I)) & ((S) - 1))

inline static int ht_hash(t_key key, int size) {
    return (int)HT_HASH(key, size);
}


/**** hash table resize ****/

static void ht_resize(t_hash_table *h) {
    int i, new_hash, new_size = 2 * h->size;
    t_bucket *b, *nextb;
    t_bucket **new_bucket_ptrs =
        (t_bucket **)calloc(new_size, sizeof(t_bucket *));

    for (i = h->size - 1; i >= 0; i--) {
        for (b = h->bucket_ptrs[i]; b; b = nextb) {
            new_hash = ht_hash(b->key, new_size);
            nextb = b->next;
            b->next = new_bucket_ptrs[new_hash];
            new_bucket_ptrs[new_hash] = b;
        }
    }
    free(h->bucket_ptrs);
    h->bucket_ptrs = new_bucket_ptrs;
    h->size = new_size;
}


/**** hash table creation, initialization, destruction ****/

t_hash_table *ht_create(int size) {
    t_hash_table *h;
    h = (t_hash_table *)malloc(sizeof(t_hash_table));
    ht_init(h, size);
    return h;
}

void ht_init(t_hash_table *h, int size) {
    h->size = size;
    h->num_keys = 0;
    h->bucket_ptrs = (t_bucket **)calloc(size, sizeof(t_bucket *));
}

void ht_delete(t_hash_table *h, void (*function)(t_value *value, void *data),
               void *data) {
    int i;
    t_bucket *b, *nextb;

    for (i = 0; i < h->size; i++) {
        for (b = h->bucket_ptrs[i]; b; b = nextb) {
            if (function)
              function(&(b->value), data);
            nextb = b->next;
            ht_delete_bucket(h, b);
        }
    }
    free(h->bucket_ptrs);
    free(h);
}


/**** functions for adding, removing and manipulating (key, value) pairs ****/

t_value *ht_update(t_hash_table *h, t_key key) {
    int hash = ht_hash(key, h->size);
    t_bucket *b = ht_find_bucket(h, key, hash);
    t_value value;
    value.ull = 0ULL;

    if (b == NULL) {
        if (h->num_keys == h->size) {
            ht_resize(h);
            hash = ht_hash(key, h->size);
        }
        b = ht_create_bucket(h, key, value, h->bucket_ptrs[hash]);
        h->bucket_ptrs[hash] = b;
    }
    return &(b->value);
}

t_value *ht_find(const t_hash_table *h, t_key key) {
    int hash = ht_hash(key, h->size);
    t_bucket *b = ht_find_bucket(h, key, hash);
    return b ? &(b->value) : NULL;
}

void ht_remove(t_hash_table *h, t_key key,
               void (*function)(t_value *value, void *data), void *data) {
    int hash = ht_hash(key, h->size);
    t_bucket *b, **prevnextb = &(h->bucket_ptrs[hash]);

    for (b = *prevnextb; b; b = *prevnextb) {
        if (b->key == key) {
            *prevnextb = b->next;
            if (function)
                function(&(b->value), data);
            ht_delete_bucket(h, b);
        } else
            prevnextb = &(b->next);
    }
}

void ht_map(t_hash_table *h,
            void (*function)(t_key key, t_value *value, void *data),
            void *data) {
    int i;
    t_bucket *b;

    for (i = 0; i < h->size; i++)
        for (b = h->bucket_ptrs[i]; b; b = b->next)
            function(b->key, &(b->value), data);
}

void ht_print(FILE *f, const t_hash_table *h,
              void (*function)(t_value *value, void *data), void *data) {
    int i;
    t_bucket *b;

    for (i = 0; i < h->size; i++) {
        for (b = h->bucket_ptrs[i]; b; b = b->next) {
            fprintf(f, "%10d : ", b->key);
            function(&(b->value), data);
        }
    }
}
