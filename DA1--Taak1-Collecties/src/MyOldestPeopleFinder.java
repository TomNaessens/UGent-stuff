/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */


import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.TreeSet;

/**
 *
 * @author tnnaesse
 */
class MyOldestPeopleFinder implements OldestPeopleFinder {

	private HashMap<String, TreeSet<MyOldestPerson>> personen;

	public MyOldestPeopleFinder() {
		personen = new HashMap();
	}

	public void addPerson(String[] person) {
		TreeSet<MyOldestPerson> tempSet;

		/*
		 * Als er al een persoonlijst bestaat haalt hij de lijst op,
		 * anders maakt hij een nieuwe lijst aan. Daarna wordt de
		 * nieuwe persoon aan de lijst toe.
		 */
		if (personen.containsKey(person[4])) {
			tempSet = personen.get(person[4]);
		} else {
			tempSet = new TreeSet();
		}
		tempSet.add(new MyOldestPerson(person));

		personen.put(person[4], tempSet);
	}

	public Collection<String> findOldestPeople(String place, int n) {
		Collection<String> id;

		id = new ArrayList();

		int persoonleeftijd = 0;
		int i = 0;

		/*
		 * De personen, gesorteerd op leeftijd die bij een gemeente horen worden overlopen.
		 * Als het maximaal aantal terug te geven personen nog niet overschreden is voegt hij het ID
		 * van de persoon toe aan de de terug te geven lijst. Hij houdt ook de leeftijd bij
		 * van de minst jonge terug te geven persoon zodat bij een ex eaquo alle personen
		 * terug gegeven worden.
		 * Als uiteindelijk het aantal terug te geven personen overschreden is, en de leeftijd
		 * van de huidige persoon komt niet meer overeen met de jongste terug te geven persoon
		 * wordt de lus afgebroken.
		 * Als het aantal gevraagde personen groter is dan het aantal personen in de lijst zal
		 * hij gewoonweg alles overlopen en alle personen van die gemeente terug geven.
		 */
		for (MyOldestPerson persoon : personen.get(place)) {
			if (i < n || persoon.getLeeftijd() == persoonleeftijd) {
				persoonleeftijd = persoon.getLeeftijd();
				id.add(persoon.getID());
				i++;
			} else {
				break;
			}
		}

		return id;
	}
}
