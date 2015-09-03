package models;

import utils.LangMessages;

/**
 * This enum represents the different statusses a
 * Pupil can have when participating in a quiz
 */
public enum Status {
    READY,          // The pupil is ready to compete in this quiz
    STARTED,        // The pupil has started this quiz
    FINISHED;       // The pupil has finished this quiz

    @Override
    public String toString() {
        return LangMessages.get("enum.status." + name());
    }
}
