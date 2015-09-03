/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package userManagement;

import java.util.ArrayList;
import java.util.GregorianCalendar;

/**
 *
 * @author NVH
 */
public interface UserInterface {
    public String getAlias();
    public String showHighScores();
    public void addHighScore(int score, GregorianCalendar date, String game);
    public void addHighScore(HighScore highScore);
    public String getHashPassWord();
    public ArrayList<Friend> getFriends();
}
