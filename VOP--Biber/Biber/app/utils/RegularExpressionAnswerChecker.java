package utils;

import java.util.regex.Pattern;

public class RegularExpressionAnswerChecker extends AnswerChecker {
    @Override
    public boolean isCorrectAnswer(String correctAnswer, String givenAnswer) {
        return Pattern.matches(correctAnswer, givenAnswer);
    }
}
