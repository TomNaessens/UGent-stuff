import java.util.ArrayList;
import java.util.Collections;

/**
 *
 * @author tnnaesse
 */
class ListInitialsCounter implements InitialsCounter {

	private ArrayList<String> personen;

	public ListInitialsCounter() {
		// Initieert de variabelen
		personen = new ArrayList();
	}

	public void addPerson(String[] person) {
		//Voornaam in stukken splitsen en van alles het eerste karakter nemen
		String[] voornaam = person[1].split(" ");
		String initialen = "";
		for (int i = 0; i < voornaam.length; i++) {
			initialen += voornaam[i].charAt(0);
		}

		//Achternaam in stukken splitsen en van alles het eerste karakter nemen
		String[] familienaam = person[2].split(" ");
		for (int i = 0; i < familienaam.length; i++) {
			initialen += familienaam[i].charAt(0);
		}

		//Initialen aan de lijst toevoegen
		personen.add(initialen);
	}

	public int getNrOccurrences(String initials) {
		return Collections.frequency(personen, initials);
	}
}
