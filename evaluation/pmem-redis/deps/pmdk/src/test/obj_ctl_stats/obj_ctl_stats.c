/*
 * Copyright 2017, Intel Corporation
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *
 *     * Redistributions in binary form must reproduce the above copyright
 *       notice, this list of conditions and the following disclaimer in
 *       the documentation and/or other materials provided with the
 *       distribution.
 *
 *     * Neither the name of the copyright holder nor the names of its
 *       contributors may be used to endorse or promote products derived
 *       from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

/*
 * obj_ctl_stats.c -- tests for the libpmemobj statistics module
 */

#include "unittest.h"

int
main(int argc, char *argv[])
{
	START(argc, argv, "obj_ctl_stats");

	if (argc != 2)
		UT_FATAL("usage: %s file-name", argv[0]);

	const char *path = argv[1];

	PMEMobjpool *pop;
	if ((pop = pmemobj_create(path, "ctl", PMEMOBJ_MIN_POOL,
		S_IWUSR | S_IRUSR)) == NULL)
		UT_FATAL("!pmemobj_create: %s", path);

	int enabled;
	int ret = pmemobj_ctl_get(pop, "stats.enabled", &enabled);
	UT_ASSERTeq(enabled, 0);
	UT_ASSERTeq(ret, 0);

	ret = pmemobj_alloc(pop, NULL, 1, 0, NULL, NULL);
	UT_ASSERTeq(ret, 0);

	size_t allocated;
	ret = pmemobj_ctl_get(pop, "stats.heap.curr_allocated", &allocated);
	UT_ASSERTeq(allocated, 0);

	enabled = 1;
	ret = pmemobj_ctl_set(pop, "stats.enabled", &enabled);
	UT_ASSERTeq(ret, 0);

	PMEMoid oid;
	ret = pmemobj_alloc(pop, &oid, 1, 0, NULL, NULL);
	UT_ASSERTeq(ret, 0);
	size_t oid_size = pmemobj_alloc_usable_size(oid) + 16;

	ret = pmemobj_ctl_get(pop, "stats.heap.curr_allocated", &allocated);
	UT_ASSERTeq(ret, 0);
	UT_ASSERTeq(allocated, oid_size);

	pmemobj_free(&oid);

	ret = pmemobj_ctl_get(pop, "stats.heap.curr_allocated", &allocated);
	UT_ASSERTeq(ret, 0);
	UT_ASSERTeq(allocated, 0);

	pmemobj_close(pop);

	DONE(NULL);
}
