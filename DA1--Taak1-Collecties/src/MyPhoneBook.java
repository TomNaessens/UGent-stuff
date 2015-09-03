/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */


import java.util.ArrayList;
import java.util.Collection;
import java.util.Map;
import java.util.TreeMap;

/**
 *
 * @author tnaessens
 */
public class MyPhoneBook implements PhoneBook {

	private TreeMap<MyPhonePerson, ArrayList<String>> personen;

	public MyPhoneBook() {
		personen = new TreeMap<MyPhonePerson, ArrayList<String>>();
	}

	public void addPerson(String[] person) {
		/*
		 * Maakt tijdelijk een nieuwe persoon aan om te kijken als deze al bestaat;
		 * Indien hij bestaat voegt hij het telefoonnummer toe aan de persoon via de
		 * methode addPhoneNumber,
		 * als deze nog niet bestaat maakt hij een nieuwe ArrayList aan, voegt hij
		 * het telefoonnummer van de persoon eraan toe en zet hij de lijst in de
		 * TreeMap met als Key het object MyPhonePerson en als value zijn telefoon-
		 * nummer.
		 */
		MyPhonePerson tempPerson = new MyPhonePerson(person[1], person[2], person[4]);
		if (personen.containsKey(tempPerson)) {
			addPhoneNumber(person[4], person[2], person[1], person[3]);
		} else {
			ArrayList<String> tempList = new ArrayList<String>();
			tempList.add(person[3]);
			personen.put(tempPerson, tempList);
		}
	}

	public Collection<String> getNumbers(String place, String lastName, String firstName) {
		return personen.get(new MyPhonePerson(firstName, lastName, place));
	}

	public void addPhoneNumber(String place, String lastName, String firstName, String phoneNumber) {
		/*
		 * Maakt een nieuwe persoon aan en kijkt als deze wel degelijk in de lijst zit
		 * om errors te vermijden.  Als de persoon bestaat haalt hij de ArrayList van
		 * nummers op die bij de persoon hoor en voegt hij het nieuwe telefoonnummer
		 * toe aan de lijst.
		 */
		MyPhonePerson tempPerson = new MyPhonePerson(firstName, lastName, place);
		if (personen.containsKey(tempPerson)) {
			ArrayList<String> tempList = personen.get(tempPerson);
			tempList.add(phoneNumber);
		}
	}

	public void write() {
		StringBuilder sb;

		for (Map.Entry<MyPhonePerson, ArrayList<String>> entry : personen.entrySet()) {
			sb = new StringBuilder();
			sb.append(entry.getKey().getGemeente());
			sb.append(" ");
			sb.append(entry.getKey().getNaam());
			sb.append(" ");
			sb.append(entry.getKey().getVoornaam());
			for (String telnr : entry.getValue()) {
				sb.append(" ");
				sb.append(telnr);
			}

			System.out.println(sb.toString());
		}

	}
}
