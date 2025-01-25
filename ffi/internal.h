#pragma once

#include <lean/lean.h>

typedef struct {
    size_t generation; // 63 (31) bits generation, 1 bit (1 << 0) "occupied" flag
    union {
        lean_object* value;
        size_t next;
    };
} lean_pod_SlotMap_entry;

typedef struct lean_pod_FixnumSlotMap_data {
    size_t size;
    size_t capacity;
    // Must be <= firstUnused
    size_t firstEmpty;
    // Must be <= capacity
    size_t firstUnused;
    lean_pod_SlotMap_entry values[];
} lean_pod_FixnumSlotMap_data;

void lean_pod_FixnumSlotMap_finalize(void* obj);
void lean_pod_FixnumSlotMap_foreach(void* obj, b_lean_obj_arg f);


typedef struct lean_pod_Deque_data {
    // Can never be 0.
    size_t capacity;
    size_t front;
    size_t back;
    bool empty;
    lean_object* data[];
} lean_pod_Deque_data;

void lean_pod_Deque_finalize(void* deque);
void lean_pod_Deque_foreach(void* deque, b_lean_obj_arg f);
