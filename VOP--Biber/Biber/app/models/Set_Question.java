package models;

import javax.persistence.*;

import play.db.ebean.Model;

import java.util.List;

@Entity
public class Set_Question extends Model {

    @Id
    @SequenceGenerator(name="set_question_seq", sequenceName="set_question_id_seq", allocationSize=0)
    @GeneratedValue(strategy=GenerationType.SEQUENCE, generator="set_question_seq")
    public Long id;

	public Difficulties difficulty;

    // The number of points we get when giving a correct answer, this is a positive number
	public short correctPoints;
    // The number of points we lose when giving a wrong answer, this is a positive number
    public short incorrectPoints;

	@ManyToOne(cascade = CascadeType.PERSIST)
	public Question question;
    @ManyToOne(cascade = CascadeType.PERSIST)
    public Set set;

    /**
     * TODO: Check if this is the only Set_Question, what to do if there is already one? Overwrite or ignore
     */
    public Set_Question(Difficulties difficulty, short correctPoints, short incorrectPoints, Question question, Set set){
        this.difficulty = difficulty;
        this.correctPoints = correctPoints;
        this.incorrectPoints = incorrectPoints;
        this.question = question;
        this.set=set;
        this.save();
    }

    public static Finder<Long, Set_Question> find = new Finder(Long.class, Set_Question.class);

    /**
     * Method to find the Set_Question object belonging to a given Set and Question
     * In case of multiple instances we take the first one, but this is only a fail save mechanism TODO?
     * @return
     */
    public static Set_Question getSet_Question(Set set, Question q){
        return find.where().eq("set", set).eq("question", q).findUnique();
    }

    /**
     *
     * @param givenAnswer   An answer given by the user, or null in case no answer was given
     * @return              Returns the number of points we get for the
     *                      given answer
     */
    public short getPoints(String givenAnswer) {
        // When no answer is given, we give 0 points
        if (givenAnswer == null)
            return 0;

        if (question.isCorrectAnswer(givenAnswer))
            return correctPoints;

        return incorrectPoints;
    }


}
