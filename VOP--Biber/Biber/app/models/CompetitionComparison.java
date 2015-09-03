package models;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;

public class CompetitionComparison {
    public History h;
    public List<ParticipationHistory> allPh;

    public CompetitionComparison(ParticipationHistory h ){
        this.h = h;
    }

    public int getNumberOfParticipants() {
        collectParticipationHistories();
        return allPh.size();
    }

    public int getRank() {
        collectParticipationHistories();
        Collections.sort(allPh, new Comparator<History>() {
            public int compare(History a, History b) {
                return a.getTotalPoints() - b.getTotalPoints();
            }
        });
        return allPh.indexOf(h)+1;
    }

    private void collectParticipationHistories() {
        if(allPh == null)
            allPh =ParticipationHistory.getHistoryFor(h.getCompetition());
    }
}
