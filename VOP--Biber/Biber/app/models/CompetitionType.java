package models;

import utils.LangMessages;

public enum CompetitionType {
	OFFICIAL(Competition.NOTVISIBLE, false),
	LOCAL(Competition.VISIBLE, false),
	UNRESTRICTED(Competition.NOTVISIBLE, true);
	
	private final short visible;
    private boolean showResults;

    CompetitionType(short visible, boolean showResults){
        this.visible = visible;
        this.showResults = showResults;
    }

	public short visible(){
		return visible;
	}

    /**
     * Indicates whether or not we are allowed to show
     * the results for this competitiontype if it is
     * not closed
     */
    public boolean showResultsWhenNotClosed() {
        return showResults;
    }
	
	public String toString(){
		return LangMessages.get("enum.competitionType." + name());
	}
	
}
