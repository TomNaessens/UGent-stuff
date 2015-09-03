#include "util.h"
#include "slp.h"
#include "prog1.h"
#include "prog2.h"
#include "prog3.h"
#include <string.h>
#include <stdio.h>

typedef struct table_ *A_table;
struct table_ {
    string id;
    int value;
    A_table tail;
};

A_table A_Table(string id, int value, A_table tail) {
    A_table t = checked_malloc(sizeof(*t));
    t->id = id;
    t->value = value;
    t->tail = tail;
    return t;
}

int lookup(A_table t, string key) {
    A_table i;
    for (i = t; i != 0; i = i->tail) {
        if (strcmp(i->id, key) == 0) {
            return i->value;
        }
    }
    return -1;
}

A_table update(A_table t, string key, int value) {
    return A_Table(key, value, t);
}


struct IntAndTable {
    int i;
    A_table t;
};
struct IntAndTable interpExp(A_exp e, A_table t);
struct IntAndTable interpStm(A_stm e, A_table t);

struct IntAndTable interpExp(A_exp e, A_table t) {
    struct IntAndTable result = { 0, t };

    struct IntAndTable opLeftIaT;
    struct IntAndTable opRightIaT;

    struct IntAndTable eseqIaT;

    /* Get the correct kind of expression */
    switch(e->kind)
    {
      case A_idExp:
        result.i = lookup(t, e->u.id);
        break;

      case A_numExp:
        result.i = e->u.num;
        break;

      case A_opExp:
        /* Get the correct kind of operation */
        opLeftIaT = interpExp(e->u.op.left, t);


        opRightIaT = interpExp(e->u.op.right, t);

        switch(e->u.op.oper)
        {
          case A_plus:
            result.i = opLeftIaT.i + opRightIaT.i;
            break;
          case A_minus:
            result.i = opLeftIaT.i - opRightIaT.i;
            break;
          case A_times:
            result.i = opLeftIaT.i * opRightIaT.i;
            break;
          case A_div:
            result.i = opLeftIaT.i / opRightIaT.i;
            break;
        }
        break;

      case A_eseqExp:
        eseqIaT = interpStm(e->u.eseq.stm, t);
        return interpExp(e->u.eseq.exp, eseqIaT.t);
    }

    return result;
}

struct IntAndTable interpStm(A_stm s, A_table t) {
    struct IntAndTable result = { 0, t };

    struct IntAndTable compoundIaTstm1;
    struct IntAndTable compoundIaTstm2;

    struct A_expList_ *currentPrint;
    int i = 0;

    switch(s->kind)
    {
      case A_compoundStm:
        compoundIaTstm1 = interpStm(s->u.compound.stm1, t);
        compoundIaTstm2 = interpStm(s->u.compound.stm2, compoundIaTstm1.t);
        result.t = compoundIaTstm2.t;
        break;

      case A_assignStm:
        result.t = update(t, s->u.assign.id, interpExp(s->u.assign.exp, t).i);
        break;

      case A_printStm:
        currentPrint = s->u.print.exps;

        while(currentPrint->kind == A_pairExpList)
        {
          result = interpExp(currentPrint->u.pair.head, result.t);
          printf("%i ", result.i);

          currentPrint = currentPrint->u.pair.tail;
        }

        result = interpExp(currentPrint->u.last, result.t);
        printf("%i\n", result.i);

        break;
    }

    return result;
}

void interp(A_stm s) {
    A_table empty_table = 0;
    interpStm(s, empty_table);
}

int main() {
    printf("\nOutput program 1:\n");
    printf("-----------------\n\n");
    interp(prog());
    printf("\nOutput program 2:\n");
    printf("-----------------\n\n");
    interp(prog2());
    printf("\nOutput program 3:\n");
    printf("-----------------\n\n");
    interp(prog3());
    printf("\n");
    return 0;
}
