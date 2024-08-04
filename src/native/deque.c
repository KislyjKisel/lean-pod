#include "include/lean_pod.h"
#include "internal.h"

void lean_pod_Deque_finalize(void* obj) {
    lean_pod_Deque_data* deque_c = (lean_pod_Deque_data*)obj;
    if (!deque_c->empty) {
        if (deque_c->front < deque_c->back) {
            for (size_t i = deque_c->front; i < deque_c->back; ++i) {
                lean_dec(deque_c->data[i]);
            }
        }
        else {
            for (size_t i = 0; i < deque_c->back; ++i) {
                lean_dec(deque_c->data[i]);
            }
            for (size_t i = deque_c->front; i < deque_c->capacity; ++i) {
                lean_dec(deque_c->data[i]);
            }
        }
    }
    free(obj);
}

void lean_pod_Deque_foreach(void* obj, b_lean_obj_arg f) {
    lean_pod_Deque_data* deque_c = (lean_pod_Deque_data*)obj;
    if (!deque_c->empty) {
        if (deque_c->front < deque_c->back) {
            lean_inc_ref_n(f, deque_c->back - deque_c->front);
            for (size_t i = deque_c->front; i < deque_c->back; ++i) {
                lean_apply_1(f, deque_c->data[i]);
            }
        }
        else {
            lean_inc_ref_n(f, deque_c->back + (deque_c->capacity - deque_c->front));
            for (size_t i = deque_c->front; i < deque_c->capacity; ++i) {
                lean_apply_1(f, deque_c->data[i]);
            }
            for (size_t i = 0; i < deque_c->back; ++i) {
                lean_apply_1(f, deque_c->data[i]);
            }
        }
    }
}

static const size_t lean_pod_Deque_initial_capacity = 4;

// If capacity is less than initial, allocates with initial capacity instead.
static inline lean_pod_Deque_data* lean_pod_Deque_alloc_c(size_t capacity) {
    if (capacity < lean_pod_Deque_initial_capacity) capacity = lean_pod_Deque_initial_capacity;
    lean_pod_Deque_data* deque = malloc(sizeof(lean_pod_Deque_data) + capacity * sizeof(lean_object*));
    deque->capacity = capacity;
    deque->empty = true;
    deque->front = 0;
    deque->back = 0;
    return deque;
}

static inline lean_pod_Deque lean_pod_Deque_alloc(size_t capacity) {
    return lean_alloc_external(lean_pod_Deque_class, lean_pod_Deque_alloc_c(capacity));
}

static inline lean_obj_res lean_pod_Deque_clone(b_lean_obj_arg deque1) {
    lean_pod_Deque_data* deque1_c = lean_pod_Deque_fromRepr(deque1);
    lean_object* deque2 = lean_pod_Deque_alloc(deque1_c->capacity);
    if (deque1_c->empty) {
        return deque2;
    }
    lean_pod_Deque_data* deque2_c = lean_pod_Deque_fromRepr(deque2);
    size_t j = 0;
    if (deque1_c->front < deque1_c->back) {
        for (size_t i = deque1_c->front; i < deque1_c->back; ++i) {
            lean_inc(deque1_c->data[i]);
            deque2_c->data[j++] = deque1_c->data[i];
        }
    }
    else {
        for (size_t i = deque1_c->front; i < deque1_c->capacity; ++i) {
            lean_inc(deque1_c->data[i]);
            deque2_c->data[j++] = deque1_c->data[i];
        }
        for (size_t i = 0; i < deque1_c->back; ++i) {
            lean_inc(deque1_c->data[i]);
            deque2_c->data[j++] = deque1_c->data[i];
        }
    }
    deque2_c->back = j;
    deque2_c->empty = false;
    return deque2;
}

static inline size_t lean_pod_Deque_next_index(size_t cap, size_t i) {
    return (i + 1) == cap ? 0 : (i + 1);
}

static inline size_t lean_pod_Deque_prev_index(size_t cap, size_t i) {
    return (i == 0 ? cap : i) - 1;
}

LEAN_EXPORT lean_obj_res lean_pod_Deque_mkEmpty(b_lean_obj_arg capacity) {
    return lean_pod_Deque_alloc(lean_usize_of_nat(capacity));
}

LEAN_EXPORT lean_obj_res lean_pod_Deque_singleton(lean_obj_arg value) {
    lean_object* deque = lean_pod_Deque_alloc(lean_pod_Deque_initial_capacity);
    lean_pod_Deque_data* deque_ = (lean_pod_Deque_data*)lean_get_external_data(deque);
    deque_->data[0] = value;
    deque_->back = lean_pod_Deque_initial_capacity > 1 ? 1 : 0;
    deque_->empty = false;
    return deque;
}

LEAN_EXPORT lean_obj_res lean_pod_Deque_replicate(b_lean_obj_arg size, b_lean_obj_arg value) {
    if (!lean_is_scalar(size)) {
        lean_internal_panic_out_of_memory();
    }
    size_t size_ = lean_unbox(size);
    lean_object* deque = lean_pod_Deque_alloc(size_);
    lean_pod_Deque_data* deque_c = (lean_pod_Deque_data*)lean_get_external_data(deque);
    lean_inc_n(value, size_);
    for (size_t i = 0; i < size_; ++i) {
        deque_c->data[i] = value;
    }
    deque_c->empty = false;
    return deque;
}

LEAN_EXPORT lean_obj_res lean_pod_Deque_toArray(b_lean_obj_arg deque) {
    lean_pod_Deque_data* deque_c = (lean_pod_Deque_data*)lean_get_external_data(deque);
    if (deque_c->front >= deque_c->back) {
        if (deque_c->empty) {
            return lean_alloc_array(0, 0);
        }
        size_t size = deque_c->back + (deque_c->capacity - deque_c->front);
        lean_object* arr = lean_alloc_array(size, size);
        size_t j = 0;
        for (size_t i = deque_c->front; i < deque_c->capacity; ++i) {
            lean_inc(deque_c->data[i]);
            lean_array_set_core(arr, j++, deque_c->data[i]);
        }
        for (size_t i = 0; i < deque_c->back; ++i) {
            lean_inc(deque_c->data[i]);
            lean_array_set_core(arr, j++, deque_c->data[i]);
        }
        return arr;
    }
    size_t size = deque_c->back - deque_c->front;
    lean_object* arr = lean_alloc_array(size, size);
    for (size_t i = deque_c->front; i < deque_c->back; ++i) {
        lean_inc(deque_c->data[i]);
        lean_array_set_core(arr, i - deque_c->front, deque_c->data[i]);
    }
    return arr;
}

LEAN_EXPORT lean_obj_res lean_pod_Deque_ofArray(b_lean_obj_arg arr) {
    size_t size = lean_array_size(arr);
    lean_object* deque = lean_pod_Deque_alloc(size);
    lean_pod_Deque_data* deque_c = (lean_pod_Deque_data*)lean_get_external_data(deque);
    deque_c->empty = size == 0;
    for (size_t i = 0; i < size; ++i) {
        lean_object* value = lean_array_get_core(arr, i);
        lean_inc(value);
        deque_c->data[i] = value;
    }
    return deque;
}

LEAN_EXPORT lean_obj_res lean_pod_Deque_ofList(b_lean_obj_arg lst) {
    if (lean_is_scalar(lst)) {
        return lean_pod_Deque_alloc(0);
    }
    size_t size = 0;
    lean_object* lst_it = lst;
    do {
        ++size;
        lst_it = lean_ctor_get(lst_it, 1);
    }
    while (!lean_is_scalar(lst_it));
    lean_object* deque = lean_pod_Deque_alloc(size);
    lean_pod_Deque_data* deque_c = (lean_pod_Deque_data*)lean_get_external_data(deque);
    deque_c->empty = false;
    size_t i = 0;
    lst_it = lst;
    do {
        lean_object* value = lean_ctor_get(lst_it, 0);
        lean_inc(value);
        deque_c->data[i++] = value;
        lst_it = lean_ctor_get(lst_it, 1);
    }
    while (!lean_is_scalar(lst_it));
    return deque;
}

LEAN_EXPORT lean_obj_res lean_pod_Deque_toList (lean_pod_Deque deque) {
    lean_pod_Deque_data* deque_c = (lean_pod_Deque_data*)lean_get_external_data(deque);
    lean_object* lst = lean_box(0);
    if (!deque_c->empty) {
        #define LEAN_KILGA_DEQUE_TOLIST_LOOP()\
            --i;\
            lean_object* value = deque_c->data[i];\
            lean_inc(value);\
            lean_object* cons = lean_alloc_ctor(1, 2, 0);\
            lean_ctor_set(cons, 0, value);\
            lean_ctor_set(cons, 1, lst);\
            lst = cons;
        if (deque_c->back <= deque_c->front) {
            size_t i = deque_c->back;
            while (i > 0) {
                LEAN_KILGA_DEQUE_TOLIST_LOOP();
            }
            i = deque_c->capacity;
            while (i > deque_c->front) {
                LEAN_KILGA_DEQUE_TOLIST_LOOP();
            }
        }
        else {
            size_t i = deque_c->back;
            while (i > deque_c->front) {
                LEAN_KILGA_DEQUE_TOLIST_LOOP();
            }
        }
        #undef LEAN_KILGA_DEQUE_TOLIST_LOOP
    }
    return lst;
}

LEAN_EXPORT uint8_t lean_pod_Deque_isEmpty(b_lean_obj_arg deque) {
    return lean_pod_Deque_fromRepr(deque)->empty;
}

LEAN_EXPORT lean_obj_res lean_pod_Deque_size(b_lean_obj_arg deque) {
    lean_pod_Deque_data* deque_c = (lean_pod_Deque_data*)lean_get_external_data(deque);
    if (deque_c->front >= deque_c->back) {
        return deque_c->empty
            ? lean_box(0)
            : lean_usize_to_nat(deque_c->back + (deque_c->capacity - deque_c->front));
    }
    return lean_usize_to_nat(deque_c->back - deque_c->front);
}

LEAN_EXPORT lean_obj_res lean_pod_Deque_pushBack(lean_obj_arg deque, lean_obj_arg x) {
    lean_pod_Deque_data* deque_c = (lean_pod_Deque_data*)lean_get_external_data(deque);
    assert(deque_c->capacity != 0);
    if (lean_is_exclusive(deque)) {
        if (!deque_c->empty && deque_c->front == deque_c->back) {
            size_t newCap = deque_c->capacity * 2;
            lean_pod_Deque_data* deque_clone_c = lean_pod_Deque_alloc_c(newCap);
            size_t frontToCap = deque_c->capacity - deque_c->front;
            memcpy(deque_clone_c->data, deque_c->data + deque_c->front, frontToCap);
            memcpy(deque_clone_c->data + frontToCap, deque_c->data, deque_c->back);
            deque_clone_c->front = 0;
            deque_clone_c->back = lean_pod_Deque_next_index(newCap, deque_c->capacity);
            deque_clone_c->empty = false;
            deque_clone_c->data[deque_c->capacity] = x;
            free(deque_c);
            lean_to_external(deque)->m_data = deque_clone_c;
            return deque;
        }
    }
    else {
        if (!deque_c->empty && deque_c->back == deque_c->front) {
            size_t newCap = deque_c->capacity * 2;
            lean_pod_Deque deque_clone = lean_pod_Deque_alloc(newCap);
            lean_pod_Deque_data* deque_clone_c = lean_pod_Deque_fromRepr(deque_clone);
            size_t j = 0;
            for (size_t i = deque_c->front; i < deque_c->capacity; ++i) {
                lean_inc(deque_c->data[i]);
                deque_clone_c->data[j++] = deque_c->data[i];
            }
            for (size_t i = 0; i < deque_c->back; ++i) {
                lean_inc(deque_c->data[i]);
                deque_clone_c->data[j++] = deque_c->data[i];
            }
            lean_dec_ref(deque);
            deque_clone_c->data[j] = x;
            deque_clone_c->back = lean_pod_Deque_next_index(newCap, j);
            deque_clone_c->empty = false;
            return deque_clone;
        }
        lean_object* deque_clone = lean_pod_Deque_clone(deque);
        lean_dec_ref(deque);
        deque = deque_clone;
        deque_c = (lean_pod_Deque_data*)lean_get_external_data(deque_clone);
    }
    deque_c->data[deque_c->back] = x;
    deque_c->back = lean_pod_Deque_next_index(deque_c->capacity, deque_c->back);
    deque_c->empty = false;
    return deque;
}

// todo: perhaps align objects to the end of data when growing in pushFront
LEAN_EXPORT lean_obj_res lean_pod_Deque_pushFront(lean_obj_arg deque, lean_obj_arg x) {
    lean_pod_Deque_data* deque_c = (lean_pod_Deque_data*)lean_get_external_data(deque);
    assert(deque_c->capacity != 0);
    if (lean_is_exclusive(deque)) {
        if (!deque_c->empty && deque_c->front == deque_c->back) {
            size_t newCap = deque_c->capacity * 2;
            lean_pod_Deque_data* deque_clone_c = lean_pod_Deque_alloc_c(newCap);
            size_t frontToCap = deque_c->capacity - deque_c->front;
            memcpy(deque_clone_c->data + 1, deque_c->data + deque_c->front, frontToCap);
            memcpy(deque_clone_c->data + 1 + frontToCap, deque_c->data, deque_c->back);
            deque_c->front = 0;
            deque_c->back = lean_pod_Deque_next_index(newCap, deque_c->capacity);
            deque_clone_c->empty = false;
            deque_clone_c->data[0] = x;
            deque_c->capacity = newCap;
            free(deque_c);
            lean_to_external(deque)->m_data = deque_clone_c;
            return deque;
        }
    }
    else {
        if (!deque_c->empty && deque_c->back == deque_c->front) {
            size_t newCap = deque_c->capacity * 2;
            lean_pod_Deque deque_clone = lean_pod_Deque_alloc(newCap);
            lean_pod_Deque_data* deque_clone_c = lean_pod_Deque_fromRepr(deque_clone);
            deque_clone_c->data[0] = x;
            size_t j = 1;
            for (size_t i = deque_c->front; i < deque_c->capacity; ++i) {
                lean_inc(deque_c->data[i]);
                deque_clone_c->data[j++] = deque_c->data[i];
            }
            for (size_t i = 0; i < deque_c->back; ++i) {
                lean_inc(deque_c->data[i]);
                deque_clone_c->data[j++] = deque_c->data[i];
            }
            lean_dec_ref(deque);
            deque_clone_c->back = j == newCap ? 0 : j;
            deque_clone_c->empty = false;
            return deque_clone;
        }
        lean_object* deque_clone = lean_pod_Deque_clone(deque);
        lean_dec_ref(deque);
        deque = deque_clone;
        deque_c = (lean_pod_Deque_data*)lean_get_external_data(deque_clone);
    }
    deque_c->front = lean_pod_Deque_prev_index(deque_c->capacity, deque_c->front);
    deque_c->data[deque_c->front] = x;
    deque_c->empty = false;
    return deque;
}

LEAN_EXPORT lean_obj_res lean_pod_Deque_peekBack(b_lean_obj_arg deque) {
    lean_pod_Deque_data* deque_c = lean_pod_Deque_fromRepr(deque);
    lean_object* value = deque_c->data[lean_pod_Deque_prev_index(deque_c->capacity, deque_c->back)];
    lean_inc(value);
    return value;
}

LEAN_EXPORT lean_obj_res lean_pod_Deque_peekFront(b_lean_obj_arg deque) {
    lean_pod_Deque_data* deque_c = lean_pod_Deque_fromRepr(deque);
    lean_object* value = deque_c->data[deque_c->front];
    lean_inc(value);
    return value;
}

LEAN_EXPORT lean_obj_res lean_pod_Deque_popBack(lean_obj_arg deque) {
    if (!lean_is_exclusive(deque)) {
        lean_object* deque_cclone = lean_pod_Deque_clone(deque);
        lean_dec_ref(deque);
        deque = deque_cclone;
    }
    lean_pod_Deque_data* deque_c = lean_pod_Deque_fromRepr(deque);
    deque_c->back = lean_pod_Deque_prev_index(deque_c->capacity, deque_c->back);
    lean_dec(deque_c->data[deque_c->back]);
    deque_c->data[deque_c->back] = NULL;
    if (deque_c->front == deque_c->back) {
        deque_c->empty = true;
    }
    return deque;
}

LEAN_EXPORT lean_obj_res lean_pod_Deque_popFront(lean_obj_arg deque) {
    if (!lean_is_exclusive(deque)) {
        lean_object* deque_clone = lean_pod_Deque_clone(deque);
        lean_dec_ref(deque);
        deque = deque_clone;
    }
    lean_pod_Deque_data* deque_c = lean_pod_Deque_fromRepr(deque);
    lean_dec(deque_c->data[deque_c->front]);
    deque_c->data[deque_c->front] = NULL;
    deque_c->front = lean_pod_Deque_next_index(deque_c->capacity, deque_c->front);
    if (deque_c->front == deque_c->back) {
        deque_c->empty = true;
    }
    return deque;
}

LEAN_EXPORT lean_obj_res lean_pod_Deque_clear(lean_obj_arg deque) {
    if(LEAN_LIKELY(lean_is_exclusive(deque))) {
        lean_pod_Deque_data* deque_c = (lean_pod_Deque_data*)lean_get_external_data(deque);
        if (deque_c->front >= deque_c->back && !deque_c->empty) {
            for (size_t i = deque_c->front; i < deque_c->capacity; ++i) {
                lean_dec(deque_c->data[i]);
                deque_c->data[i] = NULL;
            }
            for (size_t i = 0; i < deque_c->back; ++i) {
                lean_dec(deque_c->data[i]);
                deque_c->data[i] = NULL;
            }
        }
        else {
            for (size_t i = deque_c->front; i < deque_c->back; ++i) {
                lean_dec(deque_c->data[i]);
                deque_c->data[i] = NULL;
            }
        }
        deque_c->empty = true;
        deque_c->front = 0;
        deque_c->back = 0;
        return deque;
    }
    else {
        lean_dec_ref(deque);
        return lean_pod_Deque_alloc(0);
    }
}

LEAN_EXPORT lean_obj_res lean_pod_Deque_get(b_lean_obj_arg deque, b_lean_obj_arg i) {
    assert(lean_is_scalar(i));
    size_t i_ = lean_unbox(i);
    lean_pod_Deque_data* deque_c = lean_pod_Deque_fromRepr(deque);
    lean_object* value;
    if (deque_c->capacity - i_ <= deque_c->front) {
        value = deque_c->data[i_ - (deque_c->capacity - deque_c->front)];
    }
    else {
        value = deque_c->data[deque_c->front + i_];
    }
    lean_inc(value);
    return value;
}

LEAN_EXPORT lean_obj_res lean_pod_Deque_set(lean_obj_arg deque, b_lean_obj_arg i, lean_obj_arg x) {
    assert(lean_is_scalar(i));
    size_t i_ = lean_unbox(i);
    if (!lean_is_exclusive(deque)) {
        lean_object* deque_clone = lean_pod_Deque_clone(deque);
        lean_dec_ref(deque);
        deque = deque_clone;
    }
    lean_pod_Deque_data* deque_c = lean_pod_Deque_fromRepr(deque);
    lean_object** value;
    if (deque_c->capacity - i_ <= deque_c->front) {
        value = deque_c->data + (i_ - (deque_c->capacity - deque_c->front));
    }
    else {
        value = deque_c->data + (deque_c->front + i_);
    }
    lean_dec(*value);
    *value = x;
    return deque;
}
