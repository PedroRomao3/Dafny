/*===============================================
  M.EIC037: Formal Methods For Critical Systems

  Project 2 

  Your name(s): 
  ===============================================*/

include "List.dfy"

import opened L = List
  
// The next three classes have a minimal class definition,
// for simplicity
class Address {
  var value: string

  constructor(v: string)
    requires v != ""
    ensures value == v
  {
    value := v;
  }
}


class Date {
  var timestamp: int

  constructor(t: int)
    ensures timestamp == t
  {
    timestamp := t;
  }
}


class MessageId {
  var id: int

  constructor(i: int)
    ensures id == i
  {
    id := i;
  }
}


//==========================================================
//  Message
//==========================================================
class Message
{
  var id: MessageId
  var content: string
  var date: Date
  var sender: Address
  var recipients: L.List<Address>

  constructor(s: Address)
    ensures fresh(id)
    ensures fresh(date)
    ensures content == ""
    ensures sender == s
    ensures recipients == L.Nil
  {
    id := new MessageId(0);  // placeholder
    date := new Date(0);     // placeholder
    content := "";
    sender := s;
    recipients := L.Nil;
  }

  method setContent(c: string)
    modifies this
    ensures content == c
    ensures {id, date, sender} == old({id, date, sender})
    ensures recipients == old(recipients)
  {
    content := c;
  }

  method setDate(d: Date)
    modifies this
    ensures date == d
    ensures {id, sender} == old({id, sender})
    ensures recipients == old(recipients)
    ensures content == old(content)
  {
    date := d;
  }

  method addRecipient(p: nat, r: Address)
    modifies this
    requires p <= L.len(recipients) // allow adding at the end
    ensures L.len(recipients) == L.len(old(recipients)) + 1
    ensures L.elementSeq(recipients) == 
            L.elementSeq(L.take(old(recipients), p)) + [r] + L.elementSeq(L.drop(old(recipients), p))
    ensures {id, date, sender} == old({id, date, sender})
    ensures content == old(content)
  {
    recipients := InsertAt(recipients, p, r);
  }

}

// Helper function to insert an element at a given position in a List
function InsertAt<T>(l: L.List<T>, p: nat, x: T): L.List<T>
  requires p <= L.len(l)
  ensures L.len(InsertAt(l, p, x)) == L.len(l) + 1
  ensures L.elementSeq(InsertAt(l, p, x)) ==
          L.elementSeq(L.take(l, p)) + [x] + L.elementSeq(L.drop(l, p))
{
  if p == 0 then
    Cons(x, l)
  else
    match l
      case Cons(h, t) => Cons(h, InsertAt(t, p - 1, x))
      case Nil => Nil // unreachable due to requires
}





//==========================================================
//  Mailbox
//==========================================================
//
// Each Mailbox has a name, which is a string. 
// Its main content is a set of messages.
//
class Mailbox {
  var name: string
  var messages: set<Message>

  constructor(n: string)
    requires n != "" // <- Enforced here
    ensures name == n
    ensures messages == {} // <- Empty on creation
  {
    name := n;
    messages := {};
  }

  method add(m: Message)
    modifies this
    ensures messages == old(messages) + {m}
    ensures name == old(name)
  {
    messages := { m } + messages;
  }

  method remove(m: Message)
    modifies this
    ensures messages == old(messages) - {m}
    ensures name == old(name)
  {
    messages := messages - { m };
  }

  method empty()
    modifies this
    ensures messages == {}
    ensures name == old(name)
  {
    messages := {};
  }
}



//==========================================================
//  MailApp
//==========================================================

ghost function ListElements<T>(l: L.List<T>): set<T>
{
  match l
    case Nil => {}
    case Cons(h, t) => {h} + ListElements(t)
}


class MailApp {
  // abstract field for user defined boxes
  ghost var userBoxes: set<Mailbox>
  
  // abstract function returning all system mailboxes in one set
  ghost function systemBoxes(): set<Mailbox>
    reads this
  { {inbox, drafts, trash, sent} }

  // the inbox, drafts, trash and sent are both abstract and concrete
  var inbox: Mailbox
  var drafts: Mailbox
  var trash: Mailbox
  var sent: Mailbox

  // userboxList implements userBoxes 
  var userboxList: List<Mailbox>

  // Class invariant
  ghost predicate isValid() reads this {
    // 1. System mailboxes are distinct
    inbox != drafts &&
    inbox != sent &&
    inbox != trash &&
    drafts != sent &&
    drafts != trash &&
    sent != trash &&

    // 2. System mailboxes are not in user-defined set
    inbox !in userBoxes &&
    drafts !in userBoxes &&
    trash !in userBoxes &&
    sent !in userBoxes &&

    // 3. Abstract = Concrete
    userBoxes == ListElements(userboxList)
  }


  constructor ()
  {
    inbox := new Mailbox("Inbox");
    drafts := new Mailbox("Drafts");
    trash := new Mailbox("Trash");
    sent := new Mailbox("Sent");
    userboxList := Nil;
  }

  // Deletes user-defined mailbox mb
  method deleteMailbox(mb: Mailbox)
    modifies this, mb
    requires isValid()
    requires mb in userBoxes
    ensures isValid() //if we comment this line, this code works
  {
    userboxList := remove(userboxList, mb);
    userBoxes    := ListElements(userboxList);
    mb.empty();
  }




  // Adds a new mailbox with name n to set of user-defined mailboxes
  // provided that no user-defined mailbox has name n already
  method newMailbox(n: string)
    modifies this
    requires isValid()
    requires n != ""
    requires forall mb: Mailbox :: mb in userBoxes ==> mb.name != n
    ensures isValid()
  {
    var mb := new Mailbox(n);
    userboxList := Cons(mb, userboxList);
    userBoxes := ListElements(userboxList); // ghost update
  }


  // Adds a new message with sender s to the drafts mailbox
  method newMessage(s: Address)
    modifies this, drafts
    requires isValid()
    ensures isValid()
  {
    var m := new Message(s);
    drafts.add(m);
  }


  // Moves message m from mailbox mb1 to a different mailbox mb2
  method moveMessage(m: Message, mb1: Mailbox, mb2: Mailbox)
    modifies this, mb1, mb2
    requires isValid()
    ensures isValid()
  {
    mb1.remove(m);
    mb2.add(m);
  }


  // Moves message m from non-null mailbox mb to the trash mailbox
  // provided that mb is not the trash mailbox
  method deleteMessage(m: Message, mb: Mailbox)
    modifies this, mb, trash
    requires isValid()
    requires mb != trash
    ensures isValid()
  {
    moveMessage(m, mb, trash);
  }


  // Moves message m from the drafts mailbox to the sent mailbox
  method sendMessage(m: Message)
    modifies this, drafts, sent
    requires isValid()
    ensures isValid()
  {
    moveMessage(m, drafts, sent);
  }


  // Empties the trash mailbox
  method emptyTrash ()
    modifies this, trash
    requires isValid()
    ensures isValid()
  {
    trash.empty();
  }


}

// Test
/* Can be used to test your code. */
/*
method test() {

  var ma := new MailApp(); 
  assert ma.inbox.name == "Inbox";
  assert ma.drafts.name == "Drafts";
  assert ma.trash.name == "Trash";
  assert ma.sent.name == "Sent";
  assert ma.inbox.messages == ma.drafts.messages ==
                              ma.trash.messages ==
                              ma.sent.messages == {};

  ma.newMailbox("students"); 
  assert exists mb: Mailbox :: mb in ma.userBoxes &&
                               mb.name == "students" &&
                               mb.messages == {};

  var s := new Address();
  ma.newMessage(s);        
  assert exists nw: Message :: ma.drafts.messages == {nw};
}
*/
