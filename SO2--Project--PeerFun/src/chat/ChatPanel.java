/**
 *
 * @author Tom Naessens Tom.Naessens@UGent.be 2de Bachelor Informatica Universiteit Gent
 *
 */
package chat;

import java.awt.Dimension;
import javax.swing.GroupLayout;
import javax.swing.JList;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;

public class ChatPanel extends JPanel implements ChangeListener {

	private ChatModel chatModel;
	private JTextArea textArea;
	private int thisId;

	public ChatPanel(ChatModel chatModel) {

		this.chatModel = chatModel;
		thisId = 0;

		textArea = new JTextArea("", 20, 35);

		textArea.setEditable(false);
		textArea.setLineWrap(true);

		JScrollPane scrollPane = new JScrollPane(textArea);
		scrollPane.setVerticalScrollBarPolicy(JScrollPane.VERTICAL_SCROLLBAR_ALWAYS);

		JList chatList = chatModel.getChatJList();

		JScrollPane chatScrollPane = new JScrollPane(chatList);
		chatScrollPane.setPreferredSize(new Dimension(100, 0));

		GroupLayout layout = new GroupLayout(this);

		layout.setHorizontalGroup(
			 layout.createSequentialGroup().addComponent(scrollPane).addComponent(chatScrollPane));

		layout.setVerticalGroup(
			 layout.createParallelGroup().addComponent(scrollPane).addComponent(chatScrollPane));

		setLayout(layout);

		chatModel.addChangeListener(this);
	}

	@Override
	public void stateChanged(ChangeEvent ce) {
		if (thisId != getModel().getMessageId()) {
			thisId++;
			if (chatModel.getAt() != null) { // Bugfix voor de statechanged die wordt opgeroepen
				textArea.append("[" + chatModel.getAt() + "] ");
				if (chatModel.getFrom().equals("GameInfo")) {
					textArea.append("- " + chatModel.getFrom() + " - ");
				} else {
					textArea.append("<" + chatModel.getFrom() + "> ");
				}
				textArea.append(chatModel.getText() + "\n");
			}

			textArea.setCaretPosition(textArea.getText().length());
		}
	}

	public ChatModel getModel() {
		return chatModel;
	}
}
