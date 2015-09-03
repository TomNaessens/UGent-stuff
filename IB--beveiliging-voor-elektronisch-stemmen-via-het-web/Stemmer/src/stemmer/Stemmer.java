/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package stemmer;

import java.util.Arrays;

import javax.swing.JFrame;

import stemmer.gui.Venster;
import stemmer.Bijzitter;
import stemmer.Stembus;

/**
 *
 * @author cynrichuys
 */
public class Stemmer {

    /**
     * @param args the command line arguments
     */
    public static void main(String[] args) {
        java.awt.EventQueue.invokeLater(new Runnable() {
            public void run() {
                new Venster().setVisible(true);
            }
        });
    }
}
