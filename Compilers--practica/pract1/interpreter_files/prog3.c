#include "util.h"
#include "slp.h"

A_stm prog3(void) {
    return A_CompoundStm(
        A_PrintStm(A_PairExpList(
            A_EseqExp(
                A_CompoundStm(
                    A_PrintStm(A_PairExpList(
                        A_EseqExp(
                            A_AssignStm(
                                "a",
                                A_NumExp(1)
                            ),
                            A_IdExp("a")
                        ),
                        A_LastExpList(A_NumExp(3))
                    )),
                    A_AssignStm(
                        "b",
                        A_NumExp(2)
                    )
                ),
                A_IdExp("a")
            ),
            A_LastExpList(A_IdExp("a"))
        )),
        A_PrintStm(A_LastExpList(A_IdExp("b")))
    );
}
