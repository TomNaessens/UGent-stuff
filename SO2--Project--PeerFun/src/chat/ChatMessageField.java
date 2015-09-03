/**
 *
 * @author Tom Naessens
 * Tom.Naessens@UGent.be 
 * 2de Bachelor Informatica
 * Universiteit Gent
 *
 */
package chat;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import javax.swing.JTextField;
import javax.swing.event.DocumentEvent;
import javax.swing.event.DocumentListener;

class ChatMessageField extends JTextField implements ActionListener, DocumentListener {

	ChatTabbedModel chatTabbedModel;

	public ChatMessageField(ChatTabbedModel chatTabbedModel) {
		this.chatTabbedModel = chatTabbedModel;

		setColumns(20);

		addActionListener(this);
		getDocument().addDocumentListener(this);
	}

	@Override
	public void actionPerformed(ActionEvent ae) {
		sendText();
	}

	public void sendText() {
		if (getText().length() > 0) {
			chatTabbedModel.sendTextToNetworkAdapter(getText());
			setText("");
			chatTabbedModel.setButtonEnabled(false);
		}
	}

	@Override
	public void insertUpdate(DocumentEvent de) {
		textChanged();
	}

	@Override
	public void removeUpdate(DocumentEvent de) {
		textChanged();
	}

	public void textChanged() {
		chatTabbedModel.setButtonEnabled(!"".equals(getText()));
	}
	
	@Override
	public void changedUpdate(DocumentEvent de) {
	}
}
