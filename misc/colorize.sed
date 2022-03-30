1,/```/d
s,<,\&lt;,g
s,>,\&gt;,g
s,\b\(From\|Require\|Import\|Open\|Scope\|Notation\|Goal\|Proof\|Qed\|Definition\)\b,<span class="kw1">\1</span>,g
s,\b\(forall\|fun\|ltac\)\b,<span class="kw2">\1</span>,g
s,\b\(intros\|apply\|refine\|lra\)\b,<span class="kw3">\1</span>,g
s,\((\*.*\*)\),<span class="comment">\1</span>,g
s,\b\(interval\|interval_intro\|integral\|root\|plot\|Plot\)\b,<span class="kw4">\1</span>,g
