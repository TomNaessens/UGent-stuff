package ods.lab2.entities;

import java.io.Serializable;

import javax.persistence.*;
import javax.validation.constraints.NotNull;
import javax.validation.constraints.Size;

import ods.lab2.utils.Globals;

/**
 * Entity implementation class for Entity: Student
 * 
 */
@Entity
@Table(name = Globals.STUDENT_TABLE)
public class Student implements Serializable {

	private static final long serialVersionUID = 1L;

	@Id
	@GeneratedValue(strategy = GenerationType.IDENTITY)
	private Long PK_STUDENT_ID;

	@NotNull
	@Size(max = 200)
	private String name;

	@NotNull
	@Size(max = 200)
	private String surname;

	@NotNull
	@Size(max = 4)
	private int groupnumber;

	@NotNull
	@Size(max = 10)
	private int checksum;

	public Student() {
	}

	public Long getID() {
		return PK_STUDENT_ID;
	}
	
	public String getName() {
		return name;
	}

	public void setName(String name) {
		this.name = name;
	}

	public String getSurname() {
		return surname;
	}

	public void setSurname(String surname) {
		this.surname = surname;
	}

	public int getGroupnumber() {
		return groupnumber;
	}

	public void setGroupnumber(int groupnumber) {
		this.groupnumber = groupnumber;
	}

	public int getChecksum() {
		return checksum;
	}

	public void setChecksum(int checksum) {
		this.checksum = checksum;
	}

	@Override
	public String toString() {
		return "Student [PK_STUDENT_ID=" + PK_STUDENT_ID + ", name=" + name
				+ ", surname=" + surname + ", groupnumber=" + groupnumber
				+ ", checksum=" + checksum + "]";
	}

}
