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
class Mailbox { //Add specifications to the following
  var name: string
  var messages: set<Message>
 
  // Creates an empty mailbox with name n
  constructor (n: string)
  {
    name := n;
    messages := {};
  }

  // Adds message m to the mailbox
  method add(m: Message)
    modifies this
  {    
    messages := { m } + messages;
  }

  // Removes message m from mailbox
  // m need not be in the mailbox 
  method remove(m: Message)
    modifies this
  {
    messages := messages - { m };
  }

  // Empties the mailbox
  method empty()
    modifies this
  {
    messages := {};
  }
}

//==========================================================
//  MailApp
//==========================================================
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
  ghost predicate isValid() 
  {
    // replace each `true` by your formulation of the invariants 
    // described below
    //----------------------------------------------------------
    // Abstract state invariants
    //----------------------------------------------------------
    // 1. all system mailboxes (inbox, ..., sent) are distinct
    && true
    // 2. none of the system mailboxes are in the set
    //    of user-defined mailboxes
    && true
    //----------------------------------------------------------
    // Abstract-to-concrete state invariants
    //----------------------------------------------------------
    // userBoxes is the set of mailboxes in userboxList
    && true
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
  {
    userboxList := remove(userboxList, mb);
  }

  // Adds a new mailbox with name n to set of user-defined mailboxes
  // provided that no user-defined mailbox has name n already
  method newMailbox(n: string)
  {
    var mb := new Mailbox(n);
    userboxList := Cons(mb, userboxList);
  }

  // Adds a new message with sender s to the drafts mailbox
  method newMessage(s: Address)
  {
    var m := new Message(s);
    drafts.add(m);
  }

  // Moves message m from mailbox mb1 to a different mailbox mb2
  method moveMessage (m: Message, mb1: Mailbox, mb2: Mailbox)
  {
    mb1.remove(m);
    mb2.add(m);
  }

  // Moves message m from non-null mailbox mb to the trash mailbox
  // provided that mb is not the trash mailbox
  method deleteMessage (m: Message, mb: Mailbox)
  {
    moveMessage(m, mb, trash);
  }

  // Moves message m from the drafts mailbox to the sent mailbox
  method sendMessage(m: Message)
  {
    moveMessage(m, drafts, sent);
  }

  // Empties the trash mailbox
  method emptyTrash ()
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
