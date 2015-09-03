import java.util.ArrayList;

/**
 *
 * @author tnnaesse
 *
 * Klasse die een 'MyPhonePerson' persoon object aanmaakt.
 * Een MyPhonePerson is een persoon die 3 velden heeft
 * aangezien er niet meer velden nodig zijn.
 * Hier is ook een CompareTo functie aan toegevoegd om
 * personen te kunnen vergelijken op basis van gemeente,
 * naam en achternaam.
 */
public class MyPhonePerson implements Comparable<MyPhonePerson> {

	private String voornaam, naam, gemeente;

	public MyPhonePerson(String voornaam, String naam, String gemeente) {

		this.voornaam =voornaam;
		this.naam = naam;
		this.gemeente = gemeente;
	}

	public String getGemeente() {
		return gemeente;
	}

	public String getNaam() {
		return naam;
	}

	public String getVoornaam() {
		return voornaam;
	}

	public int compareTo(MyPhonePerson persoon) {
		int gemeenteCmp, naamCmp;
		gemeenteCmp = gemeente.compareToIgnoreCase(persoon.gemeente);
		if (gemeenteCmp != 0) {
			return gemeenteCmp;
		} else {
			naamCmp = naam.compareToIgnoreCase(persoon.naam);
			if (naamCmp != 0) {
				return naamCmp;
			} else {
				return voornaam.compareToIgnoreCase(persoon.voornaam);
			}
		}
	}

}
