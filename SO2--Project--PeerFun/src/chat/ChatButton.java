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
import javax.swing.JButton;
import javax.swing.JTextField;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;

class ChatButton extends JButton implements ChangeListener, ActionListener {

	ChatTabbedModel chatTabbedModel;
	ChatMessageField chatTextField;
	
	public ChatButton(ChatTabbedModel chatTabbedModel, ChatMessageField chatTextField) {
		this.chatTabbedModel = chatTabbedModel;
		this.chatTextField = chatTextField;
		
		setText("Send");
		setEnabled(false);
		
		addActionListener(this);
		chatTabbedModel.addChangeListener(this);
	}

	@Override
	public void stateChanged(ChangeEvent ce) {
		setEnabled(chatTabbedModel.getButtonEnabled());
	}

	@Override
	public void actionPerformed(ActionEvent ae) {
		chatTextField.sendText();
	}
	
}
