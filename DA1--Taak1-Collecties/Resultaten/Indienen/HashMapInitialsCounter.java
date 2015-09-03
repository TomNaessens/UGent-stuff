import java.util.HashMap;

/**
 *
 * @author tnnaesse
 */
class HashMapInitialsCounter implements InitialsCounter {

	private HashMap<String, Integer> personen;

	public HashMapInitialsCounter() {
		// Initieert de variabelen
		personen = new HashMap();
	}

	public void addPerson(String[] person) {
		// Voornaam in stukken splitsen en van alles het eerste karakter nemen
		String[] voornaam = person[1].split(" ");
		String initialen = "";
		for (int i = 0; i < voornaam.length; i++) {
			initialen += voornaam[i].charAt(0);
		}

		// Achternaam in stukken splitsen en van alles het eerste karakter nemen
		String[] familienaam = person[2].split(" ");
		for (int i = 0; i < familienaam.length; i++) {
			initialen += familienaam[i].charAt(0);
		}

		// Element aan de Hashmap toevoegen als hij er nog niet in zit, anders de waarde verhogen
		if (personen.containsKey(initialen)) {
			personen.put(initialen, personen.get(initialen) + 1);
		} else {
			personen.put(initialen, 1);
		}
	}

	public int getNrOccurrences(String initials) {
		return personen.get(initials);
	}
}
