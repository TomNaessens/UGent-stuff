package models;

import controllers.Statistics;
import play.db.ebean.*;
import javax.persistence.*;
import java.util.List;

@Entity
public class Anonymous_User_Stats extends Model{

    @Id
    public long id;

    /**
     * Number of times an anonymous user answered the question correctly
     */
    public int numberCorrect;
    /**
     * Number of times an anonymous user answered the question wrongly.
     */
    public int numberWrong;

    /**
     * Relation with Question.
     */
    @ManyToOne
    public Question question;

    /**
     * Relation with Set.
     */
    @ManyToOne
    public Set set;


    public Anonymous_User_Stats(Question question, Set set){
        this.question=question;
        this.set=set;
        numberWrong = 0;
        numberCorrect = 0;
    }

    public static Model.Finder<Long,Anonymous_User_Stats> find = new Model.Finder(Long.class, Anonymous_User_Stats.class);

    /**
     *
     * Find the Anonymous Stats object given a question and a set.
     * @param q  the Question.
     * @param s   the Set.
     * @return   the Anonymous Stats object.
     */
    public static Anonymous_User_Stats findAnonymousStats(Question q, Set s) {
        return find.where().eq("question", q).eq("set",s).findUnique();
    }

    public void incrementCorrect(){
        numberCorrect++;
    }

    public void incrementWrong(){
        numberWrong++;
    }

    public void decrementCorrect(){
        numberCorrect--;
    }

    public void decrementWrong(){
        numberWrong--;
    }

    @Override
    public String toString(){
        return question+" from set: "+set+"\n Times Correct:" +numberCorrect +", Times Wrong: "+ numberWrong;
    }
}
