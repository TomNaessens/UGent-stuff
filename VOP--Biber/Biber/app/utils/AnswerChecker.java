package utils;

import models.AnswerType;
import models.Question;

import java.util.Map;
import java.util.TreeMap;

/**
 * Instances of this class check if a given answer is correct for a
 * given answertype
 */
public abstract class AnswerChecker {
    private static final Map<AnswerType, AnswerChecker> answerMap =
            new TreeMap<AnswerType, AnswerChecker>();
    static {
        answerMap.put(AnswerType.MULTIPLE_CHOICE, new MultipleChoiceAnswerChecker());
        answerMap.put(AnswerType.REGULAR_EXPRESSION, new RegularExpressionAnswerChecker());
    }

    public abstract boolean isCorrectAnswer(String correctAnswer, String givenAnswer);

    public static AnswerChecker getAnswerChecker(AnswerType type) {
        return answerMap.get(type);
    }
}
