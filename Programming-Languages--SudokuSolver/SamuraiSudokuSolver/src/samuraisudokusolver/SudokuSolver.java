/**
 *
 * @author Tom Naessens Tom.Naessens@UGent.be 3de Bachelor Informatica Universiteit Gent
 *
 */
package samuraisudokusolver;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.logging.Level;
import java.util.logging.Logger;

class SudokuSolver implements Runnable {

    ArrayList<Integer>[][] sudoku;
    Placement placement;
    ArrayList<Integer>[][] corners;

    public SudokuSolver(Placement placement, ArrayList<Integer>[][] corners, ArrayList<Integer>[][] sudoku) {
        this.sudoku = sudoku;
        this.placement = placement;
        this.corners = corners;
    }

    @Override
    public void run() {

        boolean changed;

        do {

            do {
                changed = filter();
            } while (changed);

            synchronized (SamuraiSudokuSolver.MUTEX) {

                for (int i = 0; i < 3; i++) {
                    for (int j = 0; j < 3; j++) {
                        if (placement == Placement.UPPERLEFT) {
                            corners[i][j].retainAll(sudoku[i + 6][j + 6]);
                            sudoku[i + 6][j + 6].retainAll(corners[i][j]);
                        }
                        if (placement == Placement.UPPERRIGHT) {
                            corners[i][j + 3].retainAll(sudoku[i + 6][j]);
                            sudoku[i + 6][j].retainAll(corners[i][j + 3]);
                        }
                        if (placement == Placement.BOTTOMLEFT) {
                            corners[i + 3][j].retainAll(sudoku[i][j + 6]);
                            sudoku[i][j + 6].retainAll(corners[i + 3][j]);
                        }
                        if (placement == Placement.BOTTOMRIGHT) {
                            corners[i + 3][j + 3].retainAll(sudoku[i][j]);
                            sudoku[i][j].retainAll(corners[i + 3][j + 3]);
                        }
                        if (placement == Placement.CENTER) {
                            corners[i][j].retainAll(sudoku[i][j]);
                            sudoku[i][j].retainAll(corners[i][j]);

                            corners[i][j + 3].retainAll(sudoku[i][j + 6]);
                            sudoku[i][j + 6].retainAll(corners[i][j + 3]);

                            corners[i + 3][j].retainAll(sudoku[i + 6][j]);
                            sudoku[i + 6][j].retainAll(corners[i + 3][j]);

                            corners[i + 3][j + 3].retainAll(sudoku[i + 6][j + 6]);
                            sudoku[i + 6][j + 6].retainAll(corners[i + 3][j + 3]);
                        }
                    }
                }

                PrettyPrinter prettyPrinter = new PrettyPrinter();
                System.out.println("============================= " + placement.toString());
                prettyPrinter.prettyPrint(sudoku);

            }

        } while (!isSolved());


    }

    public boolean isSolved() {
        boolean solved = true;

        for (int i = 0; i < sudoku.length; i++) {
            for (int j = 0; j < sudoku[i].length; j++) {
                ArrayList<Integer> numberList = sudoku[i][j];
                if (numberList.size() != 1) {
                    solved = false;
                }
            }

        }

        return solved;
    }

    public boolean filter() {

        // Verwijder uit lijsten
        boolean altered = false;

        for (int i = 0; i < 9; i++) {
            for (int j = 0; j < 9; j++) {

                if (sudoku[i][j].size() == 1) {
                    boolean result = minifyLists(sudoku[i][j].get(0), i, j);
                    altered = altered || result;
                }

            }
        }

        // Is enige in rij||kolom||blok?
        boolean altered2 = false;

        for (int i = 0; i < 9; i++) {
            for (int j = 0; j < 9; j++) {

                if (sudoku[i][j].size() != 1) {
                    boolean result = isOnlyOne(i, j);
                    altered2 = altered2 || result;
                }

            }
        }

        return altered || altered2;
    }

    public boolean isOnlyOne(int i, int j) {

        boolean altered = false;

        for (Integer number : sudoku[i][j]) {

            boolean rowContains = false;
            boolean colContains = false;
            boolean blockContains = false;

            for (int k = 0; k < 9; k++) {
                if (sudoku[i][k].contains(number) && k != j) {
                    rowContains = true;
                }
                if (sudoku[k][j].contains(number) && k != i) {
                    colContains = true;
                }
            }

            // Minifyblock
            int boxLeftUpperIndexI = (i / 3) * 3;
            int boxLeftUpperIndexJ = (j / 3) * 3;

            for (int k = 0; k < 3; k++) {
                for (int l = 0; l < 3; l++) {
                    if (sudoku[k + boxLeftUpperIndexI][l + boxLeftUpperIndexJ].contains(number)
                        && !(k + boxLeftUpperIndexI == i && l + boxLeftUpperIndexJ == j)) {
                        blockContains = true;
                    }
                }
            }

            if (!rowContains || !colContains || !blockContains) {
                ArrayList<Integer> newList = new ArrayList<Integer>();
                newList.add(number);
                sudoku[i][j].retainAll(newList);
                return true;
            }

        }

        return false;
    }

    public boolean minifyLists(int number, int i, int j) {
        boolean altered = false;

        // Minifyrow
        for (int k = 0; k < 9; k++) {
            if (sudoku[i][k].contains(number) && k != j) {
                sudoku[i][k].remove(sudoku[i][k].indexOf(number));
                altered = true;
            }
            if (sudoku[k][j].contains(number) && k != i) {
                sudoku[k][j].remove(sudoku[k][j].indexOf(number));
                altered = true;
            }
        }

        // Minifyblock
        int boxLeftUpperIndexI = (i / 3) * 3;
        int boxLeftUpperIndexJ = (j / 3) * 3;

        for (int k = 0; k < 3; k++) {
            for (int l = 0; l < 3; l++) {
                if (sudoku[k + boxLeftUpperIndexI][l + boxLeftUpperIndexJ].contains(number)
                    && !(k + boxLeftUpperIndexI == i && l + boxLeftUpperIndexJ == j)) {
                    sudoku[k + boxLeftUpperIndexI][l + boxLeftUpperIndexJ].remove(sudoku[k + boxLeftUpperIndexI][l + boxLeftUpperIndexJ].indexOf(number));
                    altered = true;
                }
            }
        }

        return altered;
    }
}
