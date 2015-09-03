package models;

public interface History {

    /**
     * @return  Returns the Competition associated with this history
     */
    public Competition getCompetition();

    /**
     * @return  Returns the questionSet associated with this history
     */
    public Set getQuestionSet();

    /**
     * @return  Returns the number of milliseconds that the user has still left
     *          before the competition is finished.
     */
    public long getTimeLeft();

    /**
     * @return  Returns the number of milliseconds it took the user to
     *          complete the competition associated with this History.
     *          In case the user did not complete the competition yet,
     *          0 is returned.
     */
    public long getTotalTime();

    /**
     * @param question  Question for which we want the answer
     *
     * @return          Returns the answer the user has given to the
     *                  specified Question, or null in case no answer was
     *                  given
     */
    public String getGivenAnswer(Question question);

    /**
     * @return  Returns the total number of points the Pupil associated
     *          with this History has gotten for the answers he has given.
     */
    public int getTotalPoints();
}
