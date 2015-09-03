#include "util.h"
#include "slp.h"

A_stm prog2(void) {
    return
        /* assignments */
        A_CompoundStm(
            A_AssignStm("a", A_NumExp(8)),
            A_CompoundStm(
                A_AssignStm(
                    "aa", A_OpExp(A_OpExp(A_IdExp("a"), A_times, A_NumExp(10)),
                                  A_plus, A_IdExp("a"))),
                A_CompoundStm(
                    A_AssignStm("aaa", A_OpExp(A_OpExp(A_IdExp("aa"), A_times,
                                                       A_NumExp(10)),
                                               A_plus, A_IdExp("a"))),
                    A_CompoundStm(
                        A_AssignStm("aaaa",
                                    A_OpExp(A_OpExp(A_IdExp("aaa"), A_times,
                                                    A_NumExp(10)),
                                            A_plus, A_IdExp("a"))),
                        A_CompoundStm(
                            A_AssignStm("aaaaa",
                                        A_OpExp(A_OpExp(A_IdExp("aaaa"),
                                                        A_times, A_NumExp(10)),
                                                A_plus, A_IdExp("a"))),
                            A_CompoundStm(
                                /* line 1 */
                                A_PrintStm(A_PairExpList(
                                    A_IdExp("a"),
                                    A_PairExpList(
                                        A_IdExp("a"),
                                        A_PairExpList(
                                            A_IdExp("a"),
                                            A_PairExpList(
                                                A_IdExp("a"),
                                                A_PairExpList(
                                                    A_IdExp("a"),
                                                    A_LastExpList(
                                                        A_IdExp("a")))))))),
                                /* line 2 */
                                A_CompoundStm(
                                    A_PrintStm(A_PairExpList(
                                        A_IdExp("aa"),
                                        A_PairExpList(
                                            A_IdExp("aa"),
                                            A_PairExpList(A_IdExp("aa"),
                                                          A_LastExpList(A_IdExp(
                                                              "aa")))))),
                                    /* line 3 */
                                    A_CompoundStm(
                                        A_PrintStm(A_PairExpList(
                                            A_IdExp("aaa"),
                                            A_PairExpList(A_IdExp("aaa"),
                                                          A_LastExpList(A_IdExp(
                                                              "aaa"))))),
                                        /* line 4 */
                                        A_CompoundStm(
                                            A_PrintStm(A_PairExpList(
                                                A_IdExp("aaaaa"),
                                                A_LastExpList(
                                                    A_IdExp("aaaaa")))),
                                            /* line 3 */
                                            A_CompoundStm(
                                                A_PrintStm(A_PairExpList(
                                                    A_IdExp("aaa"),
                                                    A_PairExpList(
                                                        A_IdExp("aaa"),
                                                        A_LastExpList(
                                                            A_IdExp("aaa"))))),
                                                /* line 2 */
                                                A_CompoundStm(
                                                    A_PrintStm(A_PairExpList(
                                                        A_IdExp("aa"),
                                                        A_PairExpList(
                                                            A_IdExp("aa"),
                                                            A_PairExpList(
                                                                A_IdExp("aa"),
                                                                A_LastExpList(
                                                                    A_IdExp(
                                                                        "a"
                                                                        "a")))))),
                                                    /* line 1 */
                                                    A_PrintStm(A_PairExpList(
                                                        A_IdExp("a"),
                                                        A_PairExpList(
                                                            A_IdExp("a"),
                                                            A_PairExpList(
                                                                A_IdExp("a"),
                                                                A_PairExpList(
                                                                    A_IdExp(
                                                                        "a"),
                                                                    A_PairExpList(
                                                                        A_IdExp(
                                                                            "a"),
                                                                        A_LastExpList(A_IdExp(
                                                                            "a"))))))))
                                                    /* all done */
                                                    )))))))))));
}
