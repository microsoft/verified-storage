/*
 * Copyright 2018, Intel Corporation
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
 * obj_reorder_basic.c -- a simple unit test for store reordering
 *
 * usage: obj_reorder_basic file w|c
 * w - write data
 * c - check data consistency
 *
 */

#include "unittest.h"
#include "util.h"
#include "valgrind_internal.h"

#define LAYOUT_NAME "intro_1"
#define MAX_BUF_LEN 10
#define BUF_VALUE 'a'

struct my_root {
	size_t len;
	char buf[MAX_BUF_LEN];
};

/*
 * write_consistent -- (internal) write data in a consistent manner
 */
static void
write_consistent(struct pmemobjpool *pop)
{
	PMEMoid root = pmemobj_root(pop, sizeof(struct my_root));
	struct my_root *rootp = pmemobj_direct(root);

	char buf[MAX_BUF_LEN];
	memset(buf, BUF_VALUE, sizeof(buf));
	buf[MAX_BUF_LEN - 1] = '\0';

	rootp->len = strlen(buf);
	pmemobj_persist(pop, &rootp->len, sizeof(rootp->len));

	pmemobj_memcpy_persist(pop, rootp->buf, buf, rootp->len);
}

/*
 * check_consistency -- (internal) check buf consistency
 */
static int
check_consistency(struct pmemobjpool *pop)
{

	PMEMoid root = pmemobj_root(pop, sizeof(struct my_root));
	struct my_root *rootp = pmemobj_direct(root);

	if (rootp->len == strlen(rootp->buf) && rootp->len != 0)
		for (int i = 0; i < MAX_BUF_LEN - 1; ++i)
			if (rootp->buf[i] != BUF_VALUE)
				return 1;

	return 0;
}

int
main(int argc, char *argv[])
{
	START(argc, argv, "obj_reorder_basic");

	util_init();

	if (argc != 3 || strchr("wc", argv[1][0]) == 0 || argv[1][1] != '\0')
		UT_FATAL("usage: %s w|c file", argv[0]);

	PMEMobjpool *pop = pmemobj_open(argv[2], LAYOUT_NAME);
	UT_ASSERT(pop != NULL);

	char opt = argv[1][0];
	VALGRIND_EMIT_LOG("PMREORDER_MARKER_WRITE.BEGIN");
	switch (opt) {
		case 'w':
		{
			write_consistent(pop);
			break;
		}
		case 'c':
		{
			int ret = check_consistency(pop);
			pmemobj_close(pop);
			END(ret);
		}
		default:
			UT_FATAL("Unrecognized option %c", opt);
	}
	VALGRIND_EMIT_LOG("PMREORDER_MARKER_WRITE.END");

	pmemobj_close(pop);
	DONE(NULL);
}
