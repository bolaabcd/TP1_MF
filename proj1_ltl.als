
--===============================================
-- DCC831 Formal Methods
-- 2022.2
--
-- Miniproject 1
--
-- Names: 
--          Artur Gaspar da Silva 2020006388
--          <Colocar nome do Alan>
--
--===============================================

--------------
-- Signatures
--------------

abstract sig ObjectStatus {}
one sig InUse, Purged extends ObjectStatus {}

abstract sig Object {
  var status: lone ObjectStatus
}

sig Message extends Object {}

sig Mailbox extends Object {
  var messages: set Message
}

one sig MailApp {
  inbox: Mailbox,
  drafts: Mailbox,
  trash: Mailbox,
  sent: Mailbox,
  var userboxes: set Mailbox
}

-- added for convenience, to track the operators applied during
-- a system execution
abstract sig Operator {}
one sig CMB, DMB, CM, GM, SM, DM, MM, ET extends Operator {}
one sig Track { -- Tracking is indicated what operation just happenned
  var op: lone Operator
}


-----------------------
-- Abbreviation macros
-----------------------

-- May be convenient to use

fun mInbox []: Mailbox { MailApp.inbox }
fun mDrafts []: Mailbox { MailApp.drafts }
fun mTrash []: Mailbox { MailApp.trash }
fun mSent []: Mailbox { MailApp.sent }

fun mUserBoxes []: set Mailbox { MailApp.userboxes }

-------------
-- Operators
-------------


pred createMessage [m: Message] {
	-- preconditions
	mDrafts.status = InUse -- Draft needs to exist
	m.status = none
	all mb : Mailbox | not m in mb.messages -- it's nowhere

	-- post-conditions
	after m.status = InUse
	after m in mDrafts.messages
	
	-- frame conditions
	all ob: Object | (not m in ob) => ob.status = ob.status'
	all mb : Mailbox | mb.messages != mb.messages' => ( -- about what messages can change
		mb = mDrafts and -- only Drafts can change
		mb.messages = mb.messages' - m -- Drafts can only gain m and must not lose any messages (except m)
	)
	MailApp.userboxes = MailApp.userboxes'

	-- Tracking operation
	Track.op' = CM -- Create Message = CM
}

pred getMessage [m: Message] {
	-- preconditions
	mInbox.status = InUse -- Inbox is still valid
	m.status = none
	all mb : Mailbox | not m in mb.messages -- it's nowhere

	-- post-conditions
	after m.status = InUse
	after m in mInbox.messages

	-- frame conditions
	all ob: Object | (not m in ob) => ob.status = ob.status'
	all mb : Mailbox | mb.messages != mb.messages' => ( -- about what messages can change
		mb = mInbox and -- only Inbox can change
		mb.messages = mb.messages' - m -- Inbox can only gain m and must not lose any messages (except m)
	)
	MailApp.userboxes = MailApp.userboxes'

	-- Tracking operation
	Track.op' = GM -- Get Message = GM
}

pred moveMessage [m: Message, mb1: Mailbox] {
	-- preconditions
	mb1.status = InUse -- mb1 needs to be valid
	not m in mb1.messages
	some mb : Mailbox & status.InUse | m in mb.messages -- must be moved from some active mailbox

	-- post-conditions
	after m in mb1.messages
	all mb : Mailbox | m in mb.messages => (mb.status = InUse and after (not m in mb.messages)) -- not where it was, and it was in a valid mailbox

	-- frame conditions
	all ob: Object | ob.status = ob.status'
	all mb : Mailbox | mb.messages != mb.messages' => ( -- about what messages can change
		mb.status = InUse and -- only valid mailboxes can get or lose a message
		(mb != mb1 and (mb.messages-m) = mb.messages' )  or -- we can lose only m from mb
		(mb = mb1 and mb.messages = (mb.messages'-m) ) -- we can add only m to mb1
	)
	MailApp.userboxes = MailApp.userboxes'

	-- Tracking operation
	Track.op' = MM -- Move Message = MM	
}

pred deleteMessage [m: Message] {
	-- preconditions
	mTrash.status = InUse -- Trash needs to still be valid
	not m in mTrash.messages
	some mb : Mailbox & status.InUse | m in mb.messages -- must be moved from some active mailbox

	-- post-conditions
	after m in mTrash.messages
	all mb : Mailbox | m in mb.messages => after (not m in mb.messages) -- not where it was

	-- frame conditions
	all ob: Object | ob.status = ob.status'
	all mb : Mailbox | mb.messages != mb.messages' => ( -- about what messages can change
		mb.status = InUse and -- only valid mailboxes can get or lose a message
		(mb != mTrash and (mb.messages-m) = mb.messages' )  or -- we can lose only m from mb
		(mb = mTrash and mb.messages = (mb.messages'-m) ) -- we can add only m to the Trash
	)
	MailApp.userboxes = MailApp.userboxes'

	-- Tracking operation
	Track.op' = DM -- Delete Message = DM
}

pred sendMessage [m: Message] {
	-- preconditions
	mDrafts.status = InUse -- Draft needs to still be valid
	mSent.status = InUse -- Sent needs to still be valid
	m in mDrafts.messages

	-- post-conditions
	after m in mSent.messages
	after not m in mDrafts.messages -- not where it was

	-- frame conditions
	all ob: Object | ob.status = ob.status'
	all mb : Mailbox | mb.messages != mb.messages' => ( -- about what messages can change
		(mb = mDrafts and (mb.messages-m) = mb.messages') or -- we can lose only m from mDraft
		(mb = mSent and mb.messages = (mb.messages'-m) ) -- we can add only m to mSent
	)
	MailApp.userboxes = MailApp.userboxes'

	-- Tracking operation
	Track.op' = SM -- Send Message = SM
}

pred emptyTrash [] { -- if it's already empty, this operation does nothing
	-- preconditions
	mTrash.status = InUse -- Trash still exists

	-- post-conditions
	after mTrash.messages = none
	after all m : mTrash.messages | m.status = Purged

	-- frame conditions
	all ob: Object - mTrash.messages | ob.status = ob.status'
	all mb : Mailbox - mTrash | mb.messages = mb.messages' -- all other messages stay the same
	MailApp.userboxes = MailApp.userboxes'

	-- Tracking operation
	Track.op' = ET -- Empty Trash = ET
}

pred createMailbox [mb: Mailbox] {
	-- preconditions
	mb.status = none
	mb.messages = none
	not mb in MailApp.userboxes

	-- post-conditions
	after mb.status = InUse
	after mb.messages = none
	after mb in MailApp.userboxes

	-- frame conditions
	all ob: Object - mb | ob.status = ob.status'
	all mbx : Mailbox | mbx.messages = mbx.messages'
	MailApp.userboxes = (MailApp.userboxes' - mb) -- only mb is new, and no mailbox disappeared

	-- Tracking operation
	Track.op' = CMB -- Create Mailbox = CMB
}

pred deleteMailbox [mb: Mailbox] {
	-- preconditions
	mb.status = InUse
	mb in MailApp.userboxes

	-- post-conditions
	after not mb in MailApp.userboxes
	after mb.status = Purged
	after mb.messages = none
	all m : mb.messages | after (m.status = Purged and messages.m = none)

	-- frame conditions
	all ob: Object - (mb + mb.messages) | ob.status = ob.status'
	all mbx : Mailbox - mb | mbx.messages = mbx.messages'
	MailApp.userboxes' = (MailApp.userboxes - mb) -- only mb is lost, and no mailbox appeared

	-- Tracking operation
	Track.op' = DMB -- Delete Mailbox = DMB
}


----------------------------
-- Initial state conditions
----------------------------

pred init [] {
  -- There are no purged objects at all
	no Object.status & Purged

  -- All mailboxes are empty
	all m : Mailbox | no m.messages

  -- The predefined mailboxes are mutually distinct
	mInbox != mDrafts 
	mInbox != mTrash 
	mInbox != mSent
	mDrafts != mTrash
	mDrafts != mSent
	mTrash != mSent

  -- The predefined mailboxes are the only active objects
	all obj : Object | obj in ( mInbox + mDrafts + mTrash + mSent ) <=> obj.status = InUse

  -- The app has no user-created mailboxes
	no MailApp.userboxes

  -- For convenience, no tracked operation.
	no Track.op
}


-----------------------
-- Transition relation
-----------------------

pred trans []  {
  (some mb: Mailbox | createMailbox [mb])
  or
  (some mb: Mailbox | deleteMailbox [mb])
  or
  (some m: Message | createMessage [m])
  or
  (some m: Message | getMessage [m])
  or
  (some m: Message | sendMessage [m])
  or
  (some m: Message | deleteMessage [m])
  or
  (some m: Message | some mb: Mailbox | moveMessage [m, mb])
  or
  emptyTrash []
}



--------------------
-- System predicate
--------------------

-- Denotes all possible executions of the system from a state
-- that satisfies the initial condition
pred System {
  init
  always trans
		eventually (some mb: Mailbox | deleteMailbox [mb])
		not eventually emptyTrash []
}

run execution { System } for 8


--------------
-- Properties
--------------

pred p1 {
-- Active mailboxes contain only active messages

}

pred p2 {
-- Every active message belongs to some active mailbox

}

pred p3 {
-- Mailboxes do not share messages

}

pred p4 {
-- The system mailboxes are always active

}

pred p5 {
-- User-created mailboxes are different from the system mailboxes

}

pred p6 {
-- An object can have Purged status only if it was once active

}

pred p7 {
-- Every sent message was once a draft message

}

--------------
-- Assertions
--------------

assert a1 { System => p1 }
assert a2 { System => p2 }
assert a3 { System => p3 }
assert a4 { System => p4 }
assert a5 { System => p5 }
assert a6 { System => p6 }
assert a7 { System => p7 }
