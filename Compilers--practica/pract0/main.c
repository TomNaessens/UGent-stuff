#include "hash_table.h"
#include <stdlib.h>

#define MAX 100
void __fprint_ull(t_value *value, void *data);
void __copy_hash_tables(t_key key, t_value *value, void *data);
void __filter_select(t_key key, t_value *value, void *data);

struct key_list {
    unsigned long long *list;
    int idx;
};


int main() {
    int i;
    t_key k;

    t_hash_table *ht, *ht_copy;
    ht = ht_create(2);
    ht_copy = ht_create(2);

    /* initialize the hash table */
    for (k = 0; k < MAX; k++)
        ht_update(ht, ((k & (0xf)) ^ (k >> 2)))->ull++;

    /* print the hash table */
    fprintf(stdout, "hash table: key-value pairs %d \n", ht->num_keys);
    ht_print(stdout, ht, __fprint_ull, stdout);

    /* copy the hash table */
    ht_map(ht, __copy_hash_tables, ht_copy);

    /* make sure you can find all the keys */
    fprintf(stdout, "hash table copy: key-value pairs %d \n",
            ht_copy->num_keys);
    for (k = 0; k < MAX; k++) {
        t_value *v = ht_find(ht_copy, ((k & (0xf)) ^ (k >> 2)));
        fprintf(stdout, "found in copy %10lld :", ((k & (0xf)) ^ (k >> 2)));
        fprintf(stdout, " %10llx \n", v->ull);
    }

    /* delete the original table */
    ht_delete(ht, NULL, NULL);

    /* get a list of all the keys with a value < 3 */
    struct key_list kl;
    kl.list = calloc(ht_copy->num_keys, sizeof(unsigned long long));
    kl.idx = 0;
    ht_map(ht_copy, __filter_select, &kl);

    /* filter out the selected keys */
    for (i = 0; i < kl.idx; i++)
        ht_remove(ht_copy, kl.list[i], NULL, NULL);
    free(kl.list);

    /* print the filtered hash table copy */
    fprintf(stdout,
            "hash table copy only with values > 2 : key-value pairs %d \n",
            ht_copy->num_keys);
    ht_print(stdout, ht_copy, __fprint_ull, stdout);

    /* delete the copy */
    ht_delete(ht_copy, NULL, NULL);

    return 0;
}

void __fprint_ull(t_value *value, void *data) {
    FILE *f = (FILE *)data;
    fprintf(f, "%10llu \n", value->ull);
}

void __copy_hash_tables(t_key key, t_value *value, void *data) {
    t_hash_table *ht_copy = (t_hash_table *)data;
    ht_update(ht_copy, key)->ull = (unsigned long long)value->ull;
}

void __filter_select(t_key key, t_value *value, void *data) {
    struct key_list *kl = (struct key_list *)data;
    if (value->ull < 3)
        kl->list[kl->idx++] = key;
}
