/* Phase 9a: type-separated stored BYTE vectors. No packing or new identities. */
#ifndef MSOLVE_STORED_EXP_H
#define MSOLVE_STORED_EXP_H
typedef struct { uint8_t byte; } stored_exp_t;
_Static_assert(sizeof(stored_exp_t)==1,"byte storage layout changed");

static inline size_t stored_exp_bytes(const size_t logical_lanes)
{
    if (logical_lanes<2 || logical_lanes>128) {
        fprintf(stderr,"Error: invalid stored exponent vector length.\n");
        exit(EXIT_FAILURE);
    }
    return logical_lanes*sizeof(stored_exp_t);
}
static inline exp_t stored_exp_read(const stored_exp_t *vector,
        const size_t index,const size_t logical_lanes)
{
    if (vector==NULL || logical_lanes<2 || index>=logical_lanes || logical_lanes>128) {
        fprintf(stderr,"Error: invalid stored exponent read.\n");exit(EXIT_FAILURE);
    }
    return vector[index].byte;
}
static inline void stored_exp_write(stored_exp_t *vector,const size_t index,
        const int64_t value,const size_t logical_lanes)
{
    if (vector==NULL || logical_lanes<2 || index>=logical_lanes || logical_lanes>128) {
        fprintf(stderr,"Error: invalid stored exponent write.\n");exit(EXIT_FAILURE);
    }
    vector[index].byte=checked_exp_value(value);
}
static inline void stored_exp_import(stored_exp_t *destination,
        const exp_t *dense,const size_t logical_lanes,const size_t physical_bytes)
{
    if (destination==NULL || dense==NULL || physical_bytes!=stored_exp_bytes(logical_lanes)) {
        fprintf(stderr,"Error: invalid stored exponent import.\n");exit(EXIT_FAILURE);
    }
    /* The dense source may alias neither a stored vector nor its destination:
     * the distinct pointer types make that boundary explicit to the compiler. */
    uint32_t degree=0;
    for (size_t i=1;i<logical_lanes;++i)degree+=dense[i];
    if (degree>UINT8_MAX || dense[0]!=degree) {
        fprintf(stderr,"Error: inconsistent ordinary exponent degree.\n");exit(EXIT_FAILURE);
    }
    for (size_t i=0;i<logical_lanes;++i)destination[i].byte=dense[i];
}
static inline void stored_exp_export(exp_t *dense,const size_t logical_lanes,
        const stored_exp_t *source,const size_t physical_bytes)
{
    if (dense==NULL || source==NULL || physical_bytes!=stored_exp_bytes(logical_lanes)) {
        fprintf(stderr,"Error: invalid stored exponent export.\n");exit(EXIT_FAILURE);
    }
    for (size_t i=0;i<logical_lanes;++i)dense[i]=source[i].byte;
}
static inline void stored_exp_copy(stored_exp_t *destination,const stored_exp_t *source,
        const size_t logical_lanes,const size_t physical_bytes)
{
    if (destination==NULL || source==NULL || physical_bytes!=stored_exp_bytes(logical_lanes)) {
        fprintf(stderr,"Error: invalid stored exponent copy.\n");exit(EXIT_FAILURE);
    }
    memmove(destination,source,physical_bytes);
}
/* Private slab copies include unused slots, so they copy representation bytes
 * without interpreting degrees. The caller owns count complete vector slots. */
static inline void stored_exp_copy_vectors(stored_exp_t *destination,
        const stored_exp_t *source,const size_t logical_lanes,
        const size_t physical_bytes,const size_t count)
{
    if (destination==NULL || source==NULL ||
            physical_bytes!=stored_exp_bytes(logical_lanes) ||
            count>SIZE_MAX/physical_bytes) {
        fprintf(stderr,"Error: invalid stored exponent slab copy.\n");exit(EXIT_FAILURE);
    }
    memmove(destination,source,count*physical_bytes);
}
#endif
