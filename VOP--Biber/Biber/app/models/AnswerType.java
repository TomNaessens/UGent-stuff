package models;

import utils.LangMessages;

public enum AnswerType {
    REGULAR_EXPRESSION(1),
    MULTIPLE_CHOICE(4);
    
    private int numberOfAnswers;
    private AnswerType(int numberOfAnswers) {
    	this.numberOfAnswers = numberOfAnswers;
    }
    
    public int getNumberOfAnwsers() {
    	return numberOfAnswers;
    }
    
    public String toString() {
    	return LangMessages.get("enum.answerType."+this.name());
    }
    
    
}
