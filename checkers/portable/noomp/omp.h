/* Single-threaded stand-in for omp.h, for compilers without OpenMP (see ../intrin.h). */
#ifndef CCHK_NOOMP_H
#define CCHK_NOOMP_H
#include <time.h>
static inline double omp_get_wtime(void)
{
    struct timespec t;
    timespec_get(&t, TIME_UTC);
    return (double)t.tv_sec + 1e-9 * (double)t.tv_nsec;
}
static inline void omp_set_num_threads(int n) { (void)n; }
static inline int omp_get_thread_num(void) { return 0; }
static inline int omp_get_max_threads(void) { return 1; }
#endif
