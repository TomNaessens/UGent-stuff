/**
 *
 * @author Tom Naessens Tom.Naessens@UGent.be 3de Bachelor Informatica Universiteit Gent
 *
 */
package samuraisudokusolver;

import java.util.ArrayList;

public class PrettyPrinter {

    public void prettyPrint(ArrayList<Integer>[][] sudoku) {
        for (int i = 0; i < sudoku.length; i++) {
            for (int j = 0; j < sudoku[i].length; j++) {
                System.out.print(sudoku[i][j]);
                if(sudoku[i][j].size() < 3) {
                    System.out.print("\t");
                }
                if(sudoku[i][j].size() < 6) {
                    System.out.print("\t");
                }
            }

            if ((i + 1) % 3 == 0) {
                System.out.println("");
            }
            System.out.println("");
        }
    }
}
