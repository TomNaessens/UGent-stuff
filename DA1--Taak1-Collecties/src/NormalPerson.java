/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */


import java.util.ArrayList;

/**
 *
 * @author tnaessens
 *
 * Klasse die een 'normaal' persoon object aanmaakt.
 * Een normaal persoon is een persoon met alle velden.
 */
public class NormalPerson implements Comparable<NormalPerson> {

	private String ID, voornaam, naam, gemeente;
	private int leeftijd;
	private ArrayList<String> telefoonnummer;

	public NormalPerson(String[] person) {
		telefoonnummer = new ArrayList<String>();

		ID = person[0];
		voornaam = person[1];
		naam = person[2];
		telefoonnummer.add(person[3]);
		gemeente = person[4];
		leeftijd = Integer.parseInt(person[5]);
	}

	public String getID() {
		return ID;
	}

	public String getGemeente() {
		return gemeente;
	}

	public int getLeeftijd() {
		return leeftijd;
	}

	public String getNaam() {
		return naam;
	}

	public ArrayList<String> getTelefoonnummer() {
		return telefoonnummer;
	}

	public String getVoornaam() {
		return voornaam;
	}

	public void addTelefoonnummer(String nummer) {
		telefoonnummer.add(nummer);
	}

	public int compareTo(NormalPerson persoon) {
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
