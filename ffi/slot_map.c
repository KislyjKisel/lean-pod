#include "include/lean_pod.h"
#include "internal.h"

static inline void lean_pod_FixnumSlotMap_splitKey(lean_pod_UFixnum key, size_t iW, size_t* out_index, size_t* out_generation) {
    size_t key_c = lean_unbox(key);
    *out_index = key_c & ((1 << iW) - 1);
    *out_generation = key_c >> iW;
}

static inline lean_obj_res lean_pod_FixnumSlotMap_makeKey(size_t iW, size_t index, size_t generation) {
    return lean_pod_UFixnum_box(index | (generation << iW));
}

// Finds first valid index starting from `index` (may stop immediately at `index`).
// Returns `_ >= data->firstUnused` if no index was found.
static inline size_t lean_pod_FixnumSlotMap_nextValid_impl(lean_pod_FixnumSlotMap_data* data, size_t index) {
    while (index < data->firstUnused && (data->values[index].generation & 1) == 0) {
        index += 1;
    }
    return index;
}

static lean_obj_res lean_pod_FixnumSlotMap_alloc(size_t capacity) {
    lean_pod_FixnumSlotMap_data* data = malloc(sizeof(lean_pod_FixnumSlotMap_data) + capacity * sizeof(lean_pod_SlotMap_entry));
    data->size = 0;
    data->capacity = capacity;
    data->firstEmpty = 0;
    data->firstUnused = 0;
    return lean_alloc_external(lean_pod_FixnumSlotMap_class, data);
}

static inline lean_obj_res lean_pod_FixnumSlotMap_ensureExclusive(lean_obj_arg data) {
    if (LEAN_LIKELY(lean_is_exclusive(data))) {
        return data;
    }
    lean_pod_FixnumSlotMap_data* data_c = lean_pod_FixnumSlotMap_fromRepr(data);
    lean_object* data_clone = lean_pod_FixnumSlotMap_alloc(data_c->capacity);
    lean_pod_FixnumSlotMap_data* data_clone_c = lean_pod_FixnumSlotMap_fromRepr(data_clone);
    memcpy(data_clone_c, data_c, sizeof(lean_pod_FixnumSlotMap_data));
    for (size_t i = 0; i < data_c->firstUnused; ++i) {
        lean_pod_SlotMap_entry* x = &data_c->values[i];
        if (x->generation & 1 > 0) {
            lean_inc(x->value);
        }
        data_clone_c->values[i] = *x;
    }
    lean_dec_ref(data);
    return data_clone;
}

void lean_pod_FixnumSlotMap_finalize(void* obj) {
    lean_pod_FixnumSlotMap_data* data = obj;
    size_t index = 0;
    while(true) {
        index = lean_pod_FixnumSlotMap_nextValid_impl(data, index);
        if (index >= data->firstUnused) break;
        lean_dec(data->values[index].value);
        index += 1;
    }
    free(obj);
}

void lean_pod_FixnumSlotMap_foreach(void* obj, b_lean_obj_arg f) {
    lean_pod_FixnumSlotMap_data* data = obj;
    lean_inc_ref_n(f, data->size);
    size_t index = 0;
    while(true) {
        index = lean_pod_FixnumSlotMap_nextValid_impl(data, index);
        if (index >= data->firstUnused) break;
        lean_object* value = data->values[index].value;
        lean_inc(value);
        lean_apply_1(f, value);
        index += 1;
    }
}

LEAN_EXPORT lean_obj_res lean_pod_FixnumSlotMap_mk(
    b_lean_obj_arg iW, b_lean_obj_arg gW, b_lean_obj_arg capacity
) {
    size_t capacity_c = lean_usize_of_nat(capacity);
    lean_object* data = lean_pod_FixnumSlotMap_alloc(capacity_c);
    return data;
}

LEAN_EXPORT lean_obj_res lean_pod_FixnumSlotMap_size(
    b_lean_obj_arg iW, b_lean_obj_arg gW, lean_pod_FixnumSlotMap data
) {
    return lean_usize_to_nat(lean_pod_FixnumSlotMap_fromRepr(data)->size);
}

LEAN_EXPORT lean_obj_res lean_pod_FixnumSlotMap_top(
    b_lean_obj_arg iW, b_lean_obj_arg gW, lean_pod_FixnumSlotMap data
) {
    size_t iW_c = lean_unbox(iW);
    lean_pod_FixnumSlotMap_data* data_c = lean_pod_FixnumSlotMap_fromRepr(data);
    return lean_pod_FixnumSlotMap_makeKey(
        iW_c,
        data_c->firstEmpty,
        data_c->firstEmpty < data_c->firstUnused ? (data_c->values[data_c->firstEmpty].generation >> 1) : 0
    );
}

LEAN_EXPORT uint8_t lean_pod_FixnumSlotMap_isValid(
    b_lean_obj_arg iW, b_lean_obj_arg gW, lean_pod_FixnumSlotMap data, lean_pod_UFixnum key
) {
    lean_pod_FixnumSlotMap_data* data_c = lean_pod_FixnumSlotMap_fromRepr(data);
    size_t index, generation, iW_c = lean_usize_of_nat(iW);
    lean_pod_FixnumSlotMap_splitKey(key, iW_c, &index, &generation);
    return index < data_c->firstUnused && data_c->values[index].generation == ((generation << 1) | 1);
}

LEAN_EXPORT lean_obj_res lean_pod_FixnumSlotMap_firstValid(
    b_lean_obj_arg iW, b_lean_obj_arg gW, lean_pod_FixnumSlotMap data
) {
    lean_pod_FixnumSlotMap_data* data_c = lean_pod_FixnumSlotMap_fromRepr(data);
    size_t index = lean_pod_FixnumSlotMap_nextValid_impl(data_c, 0);
    size_t iW_c = lean_usize_of_nat(iW);
    if (index >= data_c->firstUnused) {
        return lean_box((size_t)(-1) >> 1);
    }
    return lean_pod_FixnumSlotMap_makeKey(iW_c, index, data_c->values[index].generation >> 1);
}

LEAN_EXPORT lean_obj_res lean_pod_FixnumSlotMap_nextValid(
    b_lean_obj_arg iW, b_lean_obj_arg gW, lean_pod_FixnumSlotMap data, lean_pod_UFixnum key
) {
    lean_pod_FixnumSlotMap_data* data_c = lean_pod_FixnumSlotMap_fromRepr(data);
    size_t index, generation, iW_c = lean_usize_of_nat(iW);
    lean_pod_FixnumSlotMap_splitKey(key, iW_c, &index, &generation);
    index = lean_pod_FixnumSlotMap_nextValid_impl(data_c, index + 1);
    if (index >= data_c->firstUnused) {
        return lean_box(0);
    }
    return lean_pod_FixnumSlotMap_makeKey(iW_c, index, data_c->values[index].generation >> 1);
}

LEAN_EXPORT lean_obj_res lean_pod_FixnumSlotMap_insert(
    b_lean_obj_arg iW, b_lean_obj_arg gW, lean_pod_FixnumSlotMap data, lean_obj_arg value
) {
    lean_pod_FixnumSlotMap_data* data_c = lean_pod_FixnumSlotMap_fromRepr(data);
    if (data_c->firstEmpty < data_c->capacity) {
        data = lean_pod_FixnumSlotMap_ensureExclusive(data);
        data_c = lean_pod_FixnumSlotMap_fromRepr(data);
        size_t index = data_c->firstEmpty;
        lean_pod_SlotMap_entry* entry = &data_c->values[index];
        if (index >= data_c->firstUnused) {
            data_c->firstUnused = index + 1;
            data_c->firstEmpty = index + 1; 
            entry->generation = 1;
        }
        else {
            data_c->firstEmpty = entry->next;
            entry->generation |= 1;
        }
        entry->value = value;
    }
    else {
        size_t newCapacity = 2 * data_c->capacity;
        if (newCapacity < 8) newCapacity = 8; // random initial capacity >=1?
        lean_object* newData = lean_pod_FixnumSlotMap_alloc(newCapacity);
        lean_pod_FixnumSlotMap_data* newData_c = lean_pod_FixnumSlotMap_fromRepr(newData);
        memcpy(newData_c, data_c, sizeof(lean_pod_FixnumSlotMap_data));
        for (size_t i = 0; i < data_c->firstUnused; ++i) {
            lean_pod_SlotMap_entry* entry = &data_c->values[i];
            newData_c->values[i] = *entry;
            assert(entry->generation & 1 > 0);
            lean_inc(entry->value);
        }
        newData_c->capacity = newCapacity;
        newData_c->firstEmpty = data_c->capacity + 1;
        newData_c->firstUnused = data_c->capacity + 1;
        lean_pod_SlotMap_entry* entry = &newData_c->values[data_c->capacity];
        entry->value = value;
        entry->generation |= 1;
        lean_dec_ref(data);
        data = newData;
        data_c = newData_c;
    }
    data_c->size += 1;
    return data;
}

LEAN_EXPORT lean_obj_res lean_pod_FixnumSlotMap_erase(
    b_lean_obj_arg iW, b_lean_obj_arg gW, lean_pod_FixnumSlotMap data, lean_pod_UFixnum key
) {
    data = lean_pod_FixnumSlotMap_ensureExclusive(data);
    lean_pod_FixnumSlotMap_data* data_c = lean_pod_FixnumSlotMap_fromRepr(data);
    data_c->size -= 1;
    size_t index, generation, iW_c = lean_usize_of_nat(iW);
    lean_pod_FixnumSlotMap_splitKey(key, iW_c, &index, &generation);
    lean_pod_SlotMap_entry* entry = &data_c->values[index];
    entry->next = data_c->firstEmpty;
    entry->generation = entry->generation ^ 1 + 0b10;
    data_c->firstEmpty = index;
    lean_dec(entry->value);
    return data;
}

LEAN_EXPORT lean_obj_res lean_pod_FixnumSlotMap_get(
    b_lean_obj_arg iW, b_lean_obj_arg gW, lean_pod_FixnumSlotMap data, lean_pod_UFixnum key
) {
    size_t index = lean_pod_UFixnum_unbox(key) & ((1 << lean_unbox(iW)) - 1);
    lean_object* value = lean_pod_FixnumSlotMap_fromRepr(data)->values[index].value;
    lean_inc(value);
    return value;
}

LEAN_EXPORT lean_obj_res lean_pod_FixnumSlotMap_set(
    b_lean_obj_arg iW, b_lean_obj_arg gW, lean_pod_FixnumSlotMap data, lean_pod_UFixnum key, lean_obj_arg value
) {
    data = lean_pod_FixnumSlotMap_ensureExclusive(data);
    size_t index = lean_pod_UFixnum_unbox(key) & ((1 << lean_unbox(iW)) - 1);
    lean_object** entry_value = &lean_pod_FixnumSlotMap_fromRepr(data)->values[index].value;
    lean_dec(*entry_value);
    *entry_value = value;
    return data;
}
