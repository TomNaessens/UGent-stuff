package utils;

public class MultipleChoiceAnswerChecker extends AnswerChecker {
    @Override
    public boolean isCorrectAnswer(String correctAnswer, String givenAnswer) {
        return correctAnswer.equals(givenAnswer);
    }
}
