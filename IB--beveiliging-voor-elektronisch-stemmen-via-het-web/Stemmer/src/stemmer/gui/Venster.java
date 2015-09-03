/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package stemmer.gui;

import java.awt.BorderLayout;
import java.awt.Dimension;
import java.awt.GridLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.ItemEvent;
import java.awt.event.ItemListener;
import java.awt.event.WindowEvent;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import javax.swing.BorderFactory;
import javax.swing.JButton;
import javax.swing.JCheckBox;
import javax.swing.JComboBox;
import javax.swing.JFileChooser;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JPasswordField;

import stemmer.Bijzitter;
import stemmer.Exceptions;
import stemmer.Exceptions.DeliveringFailed;
import stemmer.Stembus;
import stemmer.Vote;
import stemmer.VotingForm;
import stemmer.VotingProof;

/**
 *
 * @author cynrichuys
 */
public class Venster extends javax.swing.JFrame {

    private Bijzitter bijzitter;
    private VotingForm votingForm;
    
    private JPanel aanvraagPanel;
    private JPanel invulPanel;
    private JPanel politiciPanel;
    
    private JButton aanvraagButton;
    private JButton invulButton;
    
    private List<JCheckBox> politici = new ArrayList<JCheckBox>();
    private JComboBox<String> partijen = new JComboBox<>();

    protected static final long serialVersionUID = 1;

    /**
     * Creates new form Venster
     */
    public Venster() {
        initComponents();
        
        setLocationRelativeTo(null);
    }

    private void initComponents() {
        aanvraagPanel = new JPanel();
        invulPanel = new JPanel();
        politiciPanel = new JPanel();

        aanvraagPanel.setBorder(BorderFactory.createTitledBorder("1 - Vraag stemformulier aan"));
        invulPanel.setBorder(BorderFactory.createTitledBorder("2 - Vul stemformulier in"));

        aanvraagButton = new JButton("Stemformulier aanvragen");
        aanvraagButton.addActionListener(new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent e) {
                aanvraagButtonClicked(e);
            }
        });
        aanvraagPanel.add(aanvraagButton);
        

        invulButton = new JButton("Stemformulier indienen");
        invulButton.addActionListener(new ActionListener() {
            @Override
            public void actionPerformed(ActionEvent e) {
                invulButtonClicked(e);
            }
        });
        invulPanel.setLayout(new BorderLayout());
        invulPanel.add(partijen, BorderLayout.PAGE_START);
        invulPanel.add(politiciPanel, BorderLayout.CENTER);
        invulPanel.add(invulButton, BorderLayout.PAGE_END);
        
        getContentPane().add(aanvraagPanel, BorderLayout.PAGE_START);
        getContentPane().add(invulPanel, BorderLayout.CENTER);

        invulPanel.setVisible(false);
        
        getContentPane().setPreferredSize(new Dimension(600, 400));
        setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
        pack();
    }

    private void aanvraagButtonClicked(ActionEvent e) {
        JPanel pincodePanel = new JPanel();
        JLabel pincodeLabel = new JLabel("Geef uw pincode:");
        JPasswordField pincodeField = new JPasswordField(3);
        pincodePanel.add(pincodeLabel);
        pincodePanel.add(pincodeField);
        String[] options = new String[]{"OK", "Annuleren"};
        
        if(JOptionPane.showOptionDialog(this, 
                "<html><i>Zorg er eerst voor dat uw identeitskaartlezer "
                + "met <br>uw identiteitskaart met uw computer verbonden "
                + "is.</i></html>", "Identificeer u",
                JOptionPane.NO_OPTION, JOptionPane.PLAIN_MESSAGE,
                null, options, options[0]) == 0) 
        {
            if(JOptionPane.showOptionDialog(this, pincodePanel, "Identificeer u",
                                 JOptionPane.NO_OPTION, JOptionPane.PLAIN_MESSAGE,
                                 null, options, options[0]) == 0) // pressing OK button
            {
                String pincode = new String(pincodeField.getPassword());
                try {
                    bijzitter = new Bijzitter(pincode);
                    votingForm = bijzitter.getVotingForm();

                    aanvraagPanel.setEnabled(false);
                    aanvraagButton.setEnabled(false);

                    partijen.setModel(new javax.swing.DefaultComboBoxModel<String>(votingForm.getParties().keySet().toArray(new String[]{})));
                    partijen.addItemListener(new ItemListener() {

                        @Override
                        public void itemStateChanged(ItemEvent e) {
                            if (e.getStateChange() == ItemEvent.SELECTED) {
                                politiciPanel.removeAll();
                                politici.clear();
                                for (String politicus : votingForm.getParties().get(e.getItem())) {
                                    politici.add(new JCheckBox(politicus));
                                }
                                politiciPanel.setLayout(new GridLayout(politici.size(), 1));
                                for (JCheckBox politicus : politici) {
                                    politiciPanel.add(politicus);
                                }
                                revalidate();
                                repaint();
                            }
                        }
                    });
                    partijen.setSelectedIndex(-1);

                    invulPanel.setVisible(true);
                } catch (Exceptions.IncorrectPIN exception) {
                	JOptionPane.showMessageDialog(
                			this, 
                			"U heeft een incorrecte pincode in gegeven.\n" +
                			"Merk op dat u dit maximaal 3 maal kan doen, na de derde keer wordt uw eID geblokkeerd.", 
                			"Incorrecte pincode ingegeven",
                			JOptionPane.ERROR_MESSAGE);
                } catch (Exceptions.RetrievalFailed exception) {
                	JOptionPane.showMessageDialog(
                			this, 
                			"Er is een fout opgetreden bij het uitlezen van de data:\n" +
                			exception.getMessage(), 
                			"Fout tijdens het uitlezen",
                			JOptionPane.ERROR_MESSAGE);
                } catch (Exceptions.DuplicateVote exception) {
                	JOptionPane.showMessageDialog(
                			this, 
                			"U heeft reeds een stem uitgebracht !",
                			"U heeft reeds gestemd",
                			JOptionPane.ERROR_MESSAGE);
                } catch (Exceptions.EIDNotFound exception) {
                    JOptionPane.showMessageDialog(this,
                    	"Uw elektronische identiteitskaart kan niet worden gevonden.\n" +
                        "Controleer of the eID-reader goed aangesloten is en of uw identeitskaart\n" +
                    	"correct in de eID-reader zit:\n" + 
                        exception.getMessage(),
                        "Kaartleesfout",
                        JOptionPane.ERROR_MESSAGE);
                } 
            }
        }
    }
    
    private void invulButtonClicked(ActionEvent e) {
        List<String> voorkeursPolitici = new ArrayList<>();
        for (JCheckBox politicus : politici) {
            if (politicus.isSelected()) {
                voorkeursPolitici.add(politicus.getText());
            }
        }
        
        Vote stem = new Vote(partijen.getSelectedItem().toString(), voorkeursPolitici);
        if (Stembus.post(bijzitter, stem)) {
        	JOptionPane.showMessageDialog(
        			this, 
        			"Uw stem was succesvol toegevoegd.\n" +
        			"Indien u op OK klikt zal er een dialoog openen waarin u een locatie kan selecteren\n" +
        			"om een stembewijs op te slaan.\n" + 
        			"Gelieve dit bestand goed te bewaren, het bewijst dat u een stem heeft uitgebracht!");
        	
        	JFileChooser chooser = new JFileChooser();
        	chooser.setSelectedFile(new File("stembewijs.txt"));
        	int val = chooser.showSaveDialog(this);
        	
        	while (val != JFileChooser.APPROVE_OPTION) {
        		JOptionPane.showMessageDialog(this, "Gelieve een geldige locatie te kiezen om het stembewijs in op te slaan");
        		val = chooser.showSaveDialog(this);
        	}
        	
        	File file = chooser.getSelectedFile();
        	
        	// Get voting proof and save it
        	try {
				VotingProof proof = bijzitter.getVotingProof();
				FileWriter writer = new FileWriter(file);
				writer.write(proof.toString());
				writer.close();
				
				JOptionPane.showMessageDialog(this, "Het stembewijs is met succes opgeslagen in '" + file.getAbsolutePath() + "'");
			} catch (DeliveringFailed | IOException exception) {
				JOptionPane.showMessageDialog(this,
                    	"Er is een fout opgetreden bij het opslaan van het stembewijs:\n" +
                        exception.getMessage(),
                        "Fout bij opslaan van stembewijs",
                        JOptionPane.ERROR_MESSAGE);
			}
        }
        
        getContentPane().removeAll();
        revalidate();
        repaint();
    }
    
    private void sluitVenster(ActionEvent e) {
        dispatchEvent(new WindowEvent(this, WindowEvent.WINDOW_CLOSING));
    }
}
