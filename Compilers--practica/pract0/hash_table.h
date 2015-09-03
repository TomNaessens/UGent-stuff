#ifndef __HASH_TABLE_H
#define __HASH_TABLE_H

#include <stdio.h>

typedef unsigned long long t_key;
typedef struct s_t_bucket t_bucket;
typedef struct s_t_hash_table t_hash_table;

typedef union {
    void *p;
    char c;
    int i;
    unsigned int ui;
    long l;
    long long ll;
    unsigned long long ull;
} t_value;

struct s_t_bucket {
    t_key key;
    t_value value;
    t_bucket *next;
};

struct s_t_hash_table {
    int size;
    t_bucket **bucket_ptrs;
    int num_keys;
};


/**** hash table creation, initialization, destruction ****/
t_hash_table *ht_create(int size);
void ht_init(t_hash_table *h, int size);
void ht_delete(t_hash_table *h, void (*function)(t_value *value, void *data),
               void *data);


/**** functions for adding, removing and manipulating (key, value) pairs ****/
t_value *ht_update(t_hash_table *h, t_key key);
t_value *ht_find(const t_hash_table *h, t_key key);
void ht_remove(t_hash_table *h, t_key key,
               void (*function)(t_value *value, void *data), void *data);
void ht_map(t_hash_table *h,
            void (*function)(t_key key, t_value *value, void *data),
            void *data);
void ht_print(FILE *f, const t_hash_table *h,
              void (*function)(t_value *value, void *data), void *data);

#endif
