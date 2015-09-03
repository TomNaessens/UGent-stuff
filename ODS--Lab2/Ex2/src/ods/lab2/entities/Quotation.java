package ods.lab2.entities;

import java.io.Serializable;

import javax.persistence.*;
import javax.validation.constraints.NotNull;
import javax.validation.constraints.Size;

import ods.lab2.utils.Base64Decoder;
import ods.lab2.utils.Globals;

/**
 * Entity implementation class for Entity: Quotation
 *
 */
@Entity
@Table(name = "QUOTATION")
public class Quotation implements Serializable {

	
	private static final long serialVersionUID = 1L;
	
	@Id
	@GeneratedValue(strategy = GenerationType.IDENTITY)
	private Long PK_QUOTATION_ID;
	
	@NotNull
	@Size(max=2000)
	private String name;
	
	@NotNull
	@Size(max=2000)
	private String sentence;
	
	
	public Quotation() {
	}


	public String getName() {
		return name;
	}
	
	public void setName(String name) {
		this.name = name;
	}
	
	public String getSentence() {
		return sentence;
	}

	public void setSentence(String sentence) {
		this.sentence = sentence;
	}


	@Override
	public String toString() {
		return "Quotation [PK_QUOTATION_ID=" + PK_QUOTATION_ID + ", name="
				+ Base64Decoder.decode(name) + ", sentence=" + Base64Decoder.decode(sentence) + "]";
	}
   
}
