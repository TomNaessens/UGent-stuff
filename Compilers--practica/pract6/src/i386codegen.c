#include "codegen.h"
#include "table.h"
#include "frame.h"
#include <stdlib.h>

/*
  To get the temporaries representing the framepointer and returnvalue use:
  Temp_temp F_FP();
  Temp_temp F_RV();
*/

void munchStm(T_stm stm);
void munchExp(T_exp exp);

int munchArgs(T_expList args) {
    int i = 0;
    T_expList inv_args = NULL;

    for (; args; args = args->tail) {
        inv_args = T_ExpList(args->head, inv_args);
    }
    for (args = inv_args; args; args = args->tail) {
        munchExp(args->head);
        i++;
    }
    return i;
}

AS_instrList F_codegen(F_frame f, T_stmList stmList) {
    T_stmList iter = NULL;

    /* Procedure entry, to implement stack frame */
    printf("\tpushl\t%%ebp\n");
    printf("\tmovl\t%%esp,%%ebp\n");

    /* reserve space for the locals */
    if (f->n_locals)
        printf("\tsubl\t$%d,%%esp\n", 4 * f->n_locals);

    for (iter = stmList; iter; iter = iter->tail) {
        munchStm(iter->head);
    }

    /* clean space of the locals */
    if (f->n_locals) {
        printf("\taddl\t$%d,%%esp\n", 4 * (f->n_locals));
    }

    /* Procedure exit */
    printf("\tleave\n");
    printf("\tret\n");
    printf("\n");
    return 0;
}

void munchStm(T_stm stm) {
    switch (stm->kind) {
    case T_MOVE:
        printf("Not implemented yet! %d\n", stm->kind);
        break;
    case T_LABEL:
        printf("Not implemented yet! %d\n", stm->kind);
        break;
    case T_JUMP:
        printf("Not implemented yet! %d\n", stm->kind);
        break;
    case T_EXP:
        printf("Not implemented yet! %d\n", stm->kind);
        break;
    case T_CJUMP:
        printf("Not implemented yet! %d\n", stm->kind);
        break;
    default:
        printf("Not implemented yet! %d\n", stm->kind);
    }
}

void munchExp(T_exp exp) {
    switch (exp->kind) {
    case T_CONST:
        printf("Not handled yet, implement! %d\n", exp->kind);
        break;
    case T_BINOP:
        printf("Not handled yet, implement! %d\n", exp->kind);
        break;
    case T_MEM:
        printf("Not handled yet, implement! %d\n", exp->kind);
        break;
    case T_TEMP:
        printf("Not handled yet, implement! %d\n", exp->kind);
        break;
    case T_CALL:
        printf("Not handled yet, implement! %d\n", exp->kind);
        break;
    case T_NAME:
        printf("Not handled yet, implement! %d\n", exp->kind);
        break;
    case T_ESEQ:
        printf("Eseq found! Impossible after canonicalize");
        exit(1);
        break;
    default:
        printf("Not handled yet, implement! %d\n", exp->kind);
        // exit(1);
    }
}

/* *** DO NOT ADJUST ANYTHING BELOW ***
 * All the information needed is available above
 */

static int tempPresentInList(Temp_tempList lst, Temp_temp temp) {
    for (; lst != 0; lst = lst->tail) {
        if (lst->head == temp)
            return 1;
    }
    return 0;
}

static Temp_tempList addTemp(Temp_tempList temporariesInStmts, Temp_temp temp) {
    if (!tempPresentInList(temporariesInStmts, temp))
        return Temp_TempList(temp, temporariesInStmts);
    else
        return temporariesInStmts;
}

static Temp_tempList collectTemporariesInExpr(Temp_tempList temporariesInStmts,
                                              T_exp exp);

static Temp_tempList collectTemporariesInArgs(Temp_tempList temporariesInStmts,
                                              T_expList args) {
    for (; args; args = args->tail) {
        temporariesInStmts =
            collectTemporariesInExpr(temporariesInStmts, args->head);
    }
    return temporariesInStmts;
}

static Temp_tempList collectTemporariesInExpr(Temp_tempList temporariesInStmts,
                                              T_exp exp) {
    switch (exp->kind) {
    case T_CONST:
        break;
    case T_BINOP:
        temporariesInStmts =
            collectTemporariesInExpr(temporariesInStmts, exp->u.BINOP.left);
        temporariesInStmts =
            collectTemporariesInExpr(temporariesInStmts, exp->u.BINOP.right);
        switch (exp->u.BINOP.op) {
        case T_plus:
        case T_minus:
        case T_mul:
        case T_div:
            break;
        default:
            printf("Unexpected operator!!");
            exit(1);
        }
        break;
    case T_MEM:
        temporariesInStmts =
            collectTemporariesInExpr(temporariesInStmts, exp->u.MEM);
        break;
    case T_TEMP:
        if (exp->u.TEMP != F_FP() && exp->u.TEMP != F_RV())
            temporariesInStmts = addTemp(temporariesInStmts, exp->u.TEMP);
        break;
    case T_CALL:
        temporariesInStmts =
            collectTemporariesInArgs(temporariesInStmts, exp->u.CALL.args);
        break;
    case T_NAME:
        break;
    case T_ESEQ:
        printf("Eseq found! Impossible after canonicalize");
        exit(1);
        break;
    default:
        printf("Not handled yet, implement! %d\n", exp->kind);
    }
    return temporariesInStmts;
}

static Temp_tempList collectTemporariesInStmt(Temp_tempList temporariesInStmts,
                                              T_stm stm) {
    switch (stm->kind) {
    case T_MOVE:
        temporariesInStmts =
            collectTemporariesInExpr(temporariesInStmts, stm->u.MOVE.dst);
        temporariesInStmts =
            collectTemporariesInExpr(temporariesInStmts, stm->u.MOVE.src);
        break;
    case T_LABEL:
        break;
    case T_JUMP:
        break;
    case T_EXP:
        temporariesInStmts =
            collectTemporariesInExpr(temporariesInStmts, stm->u.EXP);
        break;
    case T_CJUMP:
        temporariesInStmts =
            collectTemporariesInExpr(temporariesInStmts, stm->u.CJUMP.left);
        temporariesInStmts =
            collectTemporariesInExpr(temporariesInStmts, stm->u.CJUMP.right);
        switch (stm->u.CJUMP.op) {
        case T_eq:
        case T_ne:
        case T_gt:
        case T_ge:
        case T_le:
        case T_lt:
            break;
        default:
            printf("Implement relOp %d\n", stm->u.CJUMP.op);
        }
        break;
    default:
        printf("Not implemented yet! %d\n", stm->kind);
        // exit(1);
    }
    return temporariesInStmts;
}

static Temp_tempList getListOfTemporaries(T_stmList stmList) {
    /** temporariesInStms is a list that is used to collect the
        set of temporaries in the stmList. */
    Temp_tempList temporariesInStmts = 0;
    T_stmList iter;
    for (iter = stmList; iter; iter = iter->tail) {
        temporariesInStmts =
            collectTemporariesInStmt(temporariesInStmts, iter->head);
    }
    /*#if 0
      {
        Temp_tempList i;
        printf ("Found following temporaries:");
        for(i=temporariesInStmts; i!=0; i=i->tail)
          printf ("T%d, ", *((int*)i->head));
        printf ("\n");
      }
    #endif*/
    return temporariesInStmts;
}

static TAB_table allocTemporaries(F_frame frame,
                                  Temp_tempList temporariesInStmts) {
    Temp_tempList i;
    TAB_table temp2F_access = TAB_empty();
    for (i = temporariesInStmts; i != 0; i = i->tail) {
        F_access tempAccess = F_allocLocal(frame, TRUE);
        TAB_enter(temp2F_access, i->head, tempAccess);
    }
    return temp2F_access;
}

static T_exp replaceTemporariesInExpr(T_exp exp, TAB_table temp2F_access);

static T_expList replaceTemporariesInArgs(T_expList args,
                                          TAB_table temp2F_access) {
    T_expList newList = 0;
    T_expList inv_args = 0;
    for (; args; args = args->tail) {
        inv_args = T_ExpList(args->head, inv_args);
    }
    for (; inv_args; inv_args = inv_args->tail) {
        newList = T_ExpList(
            replaceTemporariesInExpr(inv_args->head, temp2F_access), newList);
    }
    return newList;
}

static T_exp replaceTemporariesInExpr(T_exp exp, TAB_table temp2F_access) {
    switch (exp->kind) {
    case T_CONST:
        break;
    case T_BINOP:
        exp->u.BINOP.left =
            replaceTemporariesInExpr(exp->u.BINOP.left, temp2F_access);
        exp->u.BINOP.right =
            replaceTemporariesInExpr(exp->u.BINOP.right, temp2F_access);
        switch (exp->u.BINOP.op) {
        case T_plus:
        case T_minus:
        case T_mul:
        case T_div:
            break;
        default:
            printf("Unexpected operator!!");
            exit(1);
        }
        break;
    case T_MEM:
        exp->u.MEM = replaceTemporariesInExpr(exp->u.MEM, temp2F_access);
        break;
    case T_TEMP:
        if (exp->u.TEMP != F_FP() && exp->u.TEMP != F_RV()) {
            F_access acc = (F_access)TAB_look(temp2F_access, exp->u.TEMP);
            assert(acc != 0);
            return F_Exp(acc, T_Temp(F_FP()));
        }
        break;
    case T_CALL:
        exp->u.CALL.args =
            replaceTemporariesInArgs(exp->u.CALL.args, temp2F_access);
        break;
    case T_NAME:
        break;
    case T_ESEQ:
        printf("Eseq found! Impossible after canonicalize");
        exit(1);
        break;
    default:
        printf("Not handled yet, implement! %d\n", exp->kind);
    }
    return exp;
}

static void replaceTemporariesInStmt(T_stm stm, TAB_table temp2F_access) {
    switch (stm->kind) {
    case T_MOVE:
        stm->u.MOVE.dst =
            replaceTemporariesInExpr(stm->u.MOVE.dst, temp2F_access);
        stm->u.MOVE.src =
            replaceTemporariesInExpr(stm->u.MOVE.src, temp2F_access);
        break;
    case T_LABEL:
        break;
    case T_JUMP:
        break;
    case T_EXP:
        stm->u.EXP = replaceTemporariesInExpr(stm->u.EXP, temp2F_access);
        break;
    case T_CJUMP:
        stm->u.CJUMP.left =
            replaceTemporariesInExpr(stm->u.CJUMP.left, temp2F_access);
        stm->u.CJUMP.right =
            replaceTemporariesInExpr(stm->u.CJUMP.right, temp2F_access);
        switch (stm->u.CJUMP.op) {
        case T_eq:
        case T_ne:
        case T_gt:
        case T_ge:
        case T_le:
        case T_lt:
            break;
        default:
            printf("Implement relOp %d\n", stm->u.CJUMP.op);
        }
        break;
    default:
        printf("Not implemented yet! %d\n", stm->kind);
        // exit(1);
    }
}


static void changeTemp2localAccess(T_stmList stmList, TAB_table temp2F_access) {
    T_stmList iter;
    for (iter = stmList; iter; iter = iter->tail) {
        replaceTemporariesInStmt(iter->head, temp2F_access);
    }
}

void C_eliminateTemporariesAfterScheduling(F_frame frame, T_stmList stmList) {
    Temp_tempList temporariesInStmts = getListOfTemporaries(stmList);
    TAB_table temp2F_access = allocTemporaries(frame, temporariesInStmts);
    changeTemp2localAccess(stmList, temp2F_access);
}
