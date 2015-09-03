/**
 *
 * @author Tom Naessens Tom.Naessens@UGent.be 3de Bachelor Informatica Universiteit Gent
 *
 */
package samuraisudokusolver;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;
import java.util.logging.Level;
import java.util.logging.Logger;

public class SamuraiSudokuSolver {

    public static final Object MUTEX = new Object();
    
    public static int[][] sudoku = {
        {0, 6, 1, 0, 0, 8, 0, 3, 0, -1, -1, -1, 0, 5, 0, 2, 0, 0, 6, 9, 0},
        {9, 0, 0, 0, 4, 0, 0, 0, 0, -1, -1, -1, 0, 0, 0, 0, 8, 0, 0, 0, 5},
        {7, 0, 0, 6, 0, 0, 0, 0, 8, -1, -1, -1, 9, 0, 0, 0, 0, 6, 0, 0, 1},
        {0, 0, 9, 5, 7, 0, 0, 8, 1, -1, -1, -1, 3, 4, 0, 0, 7, 1, 9, 0, 0},
        {0, 5, 0, 1, 0, 0, 0, 7, 0, -1, -1, -1, 0, 7, 0, 0, 0, 2, 0, 8, 0},
        {6, 0, 0, 0, 0, 0, 2, 0, 0, -1, -1, -1, 0, 0, 6, 0, 0, 0, 0, 0, 7},
        {0, 0, 0, 0, 0, 3, 0, 0, 0, 9, 0, 6, 0, 0, 0, 5, 0, 0, 0, 0, 0},
        {2, 0, 0, 7, 1, 0, 0, 0, 0, 2, 0, 5, 0, 0, 0, 0, 6, 8, 0, 0, 3},
        {0, 0, 4, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 8, 0, 0},
        {-1, -1, -1, -1, -1, -1, 1, 3, 0, 8, 0, 4, 0, 5, 7, -1, -1, -1, -1, -1, -1},
        {-1, -1, -1, -1, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, -1, -1, -1, -1},
        {-1, -1, -1, -1, -1, -1, 4, 9, 0, 1, 0, 2, 0, 8, 6, -1, -1, -1, -1, -1, -1},
        {0, 0, 2, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 8, 0, 0},
        {9, 0, 0, 2, 4, 0, 0, 0, 0, 4, 0, 1, 0, 0, 0, 0, 8, 6, 0, 0, 2},
        {0, 0, 0, 0, 0, 1, 0, 0, 0, 3, 0, 7, 0, 0, 0, 2, 0, 0, 0, 0, 0},
        {6, 0, 0, 0, 0, 0, 1, 0, 0, -1, -1, -1, 0, 0, 4, 0, 0, 0, 0, 0, 6},
        {0, 9, 0, 8, 0, 0, 0, 2, 0, -1, -1, -1, 0, 1, 0, 0, 0, 4, 0, 3, 0},
        {0, 0, 4, 3, 6, 0, 0, 9, 5, -1, -1, -1, 3, 5, 0, 0, 6, 7, 4, 0, 0},
        {2, 0, 0, 6, 0, 0, 0, 0, 7, -1, -1, -1, 2, 0, 0, 0, 0, 8, 0, 0, 5},
        {5, 0, 0, 0, 7, 0, 0, 0, 0, -1, -1, -1, 0, 0, 0, 0, 7, 0, 0, 0, 1},
        {0, 6, 8, 0, 0, 2, 0, 1, 0, -1, -1, -1, 0, 9, 0, 5, 0, 0, 2, 8, 0}
    };

    public static void fillSudoku(int rowOffset, int colOffset, ArrayList<Integer>[][] arraySudoku) {
        for (int i = 0; i < 9; i++) {
            for (int j = 0; j < 9; j++) {
                arraySudoku[i][j] = new ArrayList<Integer>();
                if (sudoku[i + rowOffset][j + colOffset] == 0) {
                    arraySudoku[i][j].add(1);
                    arraySudoku[i][j].add(2);
                    arraySudoku[i][j].add(3);
                    arraySudoku[i][j].add(4);
                    arraySudoku[i][j].add(5);
                    arraySudoku[i][j].add(6);
                    arraySudoku[i][j].add(7);
                    arraySudoku[i][j].add(8);
                    arraySudoku[i][j].add(9);
                } else {
                    arraySudoku[i][j].add(sudoku[i + rowOffset][j + colOffset]);
                }
            }
        }
    }

    public static void main(String[] args) {

        ArrayList<Integer>[][] leftUpperSudoku = (ArrayList<Integer>[][]) new ArrayList[9][9];
        ArrayList<Integer>[][] rightUpperSudoku = (ArrayList<Integer>[][]) new ArrayList[9][9];
        ArrayList<Integer>[][] leftBottomSudoku = (ArrayList<Integer>[][]) new ArrayList[9][9];
        ArrayList<Integer>[][] rightBottomSudoku = (ArrayList<Integer>[][]) new ArrayList[9][9];
        ArrayList<Integer>[][] centerSudoku = (ArrayList<Integer>[][]) new ArrayList[9][9];

        ArrayList<Integer>[][] corners = (ArrayList<Integer>[][]) new ArrayList[6][6];
        for (int i = 0; i < 6; i++) {
            for (int j = 0; j < 6; j++) {
                corners[i][j] = new ArrayList<Integer>();
                corners[i][j].add(1);
                corners[i][j].add(2);
                corners[i][j].add(3);
                corners[i][j].add(4);
                corners[i][j].add(5);
                corners[i][j].add(6);
                corners[i][j].add(7);
                corners[i][j].add(8);
                corners[i][j].add(9);
            }
        }

        fillSudoku(0, 0, leftUpperSudoku);
        fillSudoku(0, 12, rightUpperSudoku);
        fillSudoku(6, 6, centerSudoku);
        fillSudoku(12, 0, leftBottomSudoku);
        fillSudoku(12, 12, rightBottomSudoku);

        List<Runnable> solverList = new ArrayList<Runnable>();
        solverList.add(new SudokuSolver(Placement.UPPERLEFT, corners, leftUpperSudoku));
        solverList.add(new SudokuSolver(Placement.UPPERRIGHT, corners, rightUpperSudoku));
        solverList.add(new SudokuSolver(Placement.BOTTOMLEFT, corners, leftBottomSudoku));
        solverList.add(new SudokuSolver(Placement.BOTTOMRIGHT, corners, rightBottomSudoku));
        solverList.add(new SudokuSolver(Placement.CENTER, corners, centerSudoku));

        for (Runnable runnable : solverList) {
            (new Thread(runnable)).start();
        }
    }
}
