import ShellWall
open System

/-! # bash → `Pipeline` parser (UNVERIFIED tooling)

Parses the closed fragment the model supports into a `Pipeline` term. This sits
ENTIRELY UPSTREAM of the verified core — it is not imported by any spec/decider/
proof module, and a parse bug can only produce the wrong `Pipeline` (which the CLI
always echoes before gating), never affect a proof.

DENY-BY-DEFAULT: anything outside the fragment ($(...), variables, globs, quotes we
don't handle, `<`, unknown commands/flags, background `&`) is REJECTED with a
message — never coerced into a nearest in-fragment term. This is a security
property: silently approximating an out-of-fragment command would gate the wrong
thing.

Supported grammar (bash precedence: `|` tightest, then `&&`/`||`, then `;`; all
left-associative):
```
  seq     := andor (';' andor)*
  andor   := pipe (('&&' | '||') pipe)*
  pipe    := elem ('|' elem)*
  elem    := ( '(' seq ')' | simpleCmd ) redirect?
  simpleCmd:
    cat <path>            → read
    grep [-F] [-e] <pat>  → grep      (model grep is substring; -F and -e accepted)
    [LC_ALL=C] sort       → sort
    uniq | wc
    rm <path> | mkdir <path>
    cat                   → (bare) identity; only valid with a redirect ⇒ write
  redirect := ('>' | '>>') <path>     → wraps the element in a write stage
```
`partial` (unverified tooling); it is total in practice on finite input. -/

namespace ShellWall.Parser

/-- A path word → `Path`. -/
private def toPath (w : String) : Path := ⟨w⟩

/-! ## Tokenizer -/

inductive Tok
  | word (s : String)
  | pipe | seq | andOp | orOp | gt | gtgt | lp | rp
  deriving Repr, BEq

private def isDelim (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '|' || c == '&' || c == ';' ||
  c == '>' || c == '<' || c == '(' || c == ')'

-- PARSE-FIDELITY: these unquoted characters trigger bash EXPANSION/GLOBBING, which
-- the model cannot represent. We reject rather than parse them literally — matching
-- bash would require implementing expansion, and a literal reading would be wrong.
private def isForbidden (c : Char) : Bool :=
  c == '$' || c == '`' || c == '"' || c == '*' || c == '?' ||
  c == '[' || c == ']' || c == '{' || c == '}' || c == '~' || c == '!' || c == '\\'

/-- Read the interior of a single-quoted string (up to the closing quote). shq-style
`'\''` escaping is handled by `readWord` concatenating adjacent segments. -/
private partial def readQuoted : List Char → String → Except String (String × List Char)
  | [], _ => .error "unterminated single quote"
  | c :: rest, acc => if c == '\'' then .ok (acc, rest) else readQuoted rest (acc.push c)

/-- Read one word (bash tokenization): unquoted chars, `'...'` segments, and `\c`
escapes, all concatenated until a delimiter. Rejects forbidden unquoted chars. -/
private partial def readWord : List Char → String → Except String (String × List Char)
  | [], acc => .ok (acc, [])
  | c :: rest, acc =>
    if c == '\'' then
      match readQuoted rest "" with
      | .error e => .error e
      | .ok (inner, rest2) => readWord rest2 (acc ++ inner)
    else if isDelim c then .ok (acc, c :: rest)
    else if isForbidden c then
      .error s!"out-of-fragment character '{c}' (shell expansion/glob not supported)"
    else readWord rest (acc.push c)

private partial def tokenize : List Char → Except String (List Tok)
  | [] => .ok []
  | c :: rest =>
    if c == ' ' || c == '\t' then tokenize rest
    else if c == '|' then
      match rest with
      | '|' :: r => (tokenize r).map (Tok.orOp :: ·)
      | _ => (tokenize rest).map (Tok.pipe :: ·)
    else if c == '&' then
      match rest with
      | '&' :: r => (tokenize r).map (Tok.andOp :: ·)
      | _ => .error "single '&' (background execution) not supported"
    else if c == ';' then (tokenize rest).map (Tok.seq :: ·)
    else if c == '>' then
      match rest with
      | '>' :: r => (tokenize r).map (Tok.gtgt :: ·)
      | _ => (tokenize rest).map (Tok.gt :: ·)
    else if c == '<' then .error "input redirection '<' not supported"
    else if c == '(' then (tokenize rest).map (Tok.lp :: ·)
    else if c == ')' then (tokenize rest).map (Tok.rp :: ·)
    else
      match readWord (c :: rest) "" with
      | .error e => .error e
      | .ok (w, rest2) =>
        if w.isEmpty then tokenize rest2 else (tokenize rest2).map (Tok.word w :: ·)

/-! ## Command mapping -/

/-- What a simple command's words denote before a possible redirect. -/
private inductive Base
  | cmd (c : Cmd)     -- a concrete command
  | bareCat           -- `cat` with no file: identity, only valid with a redirect
  | group (p : Pipeline)  -- a parenthesized sub-pipeline

/-- Parse a `grep`'s flags/pattern: `[-F] [-e] <pat>`, exactly one pattern. -/
private def parseGrep : List String → Except String Cmd
  | [] => .error "grep: missing pattern"
  | "-F" :: rest => parseGrep rest
  | "-e" :: pat :: [] => .ok (.grep pat)
  | "-e" :: _ => .error "grep: -e expects exactly one pattern"
  | pat :: [] =>
      if pat.startsWith "-" then .error s!"grep: unsupported flag '{pat}'"
      else .ok (.grep pat)
  | _ => .error "grep: only a single literal pattern is supported"

/-- Map a simple command's words to a `Base`. -/
private def wordsToBase : List String → Except String Base
  | ["cat"] => .ok .bareCat
  | ["cat", p] => .ok (.cmd (.read (toPath p)))
  | "grep" :: rest => (parseGrep rest).map .cmd
  | ["sort"] => .ok (.cmd .sort)
  | ["LC_ALL=C", "sort"] => .ok (.cmd .sort)   -- the renderer's C-locale form
  | ["uniq"] => .ok (.cmd .uniq)
  | ["wc"] => .ok (.cmd .wc)
  | ["rm", p] => .ok (.cmd (.rm (toPath p)))
  | ["mkdir", p] => .ok (.cmd (.mkdir (toPath p)))
  | [] => .error "empty command"
  | ws => .error ("unsupported command: " ++ String.intercalate " " ws)

/-- Apply an optional redirect to a base, yielding a `Pipeline`. -/
private def applyRedirect : Base → Option (WriteMode × String) → Except String Pipeline
  | .bareCat, some (m, p) => .ok (.single (.write (toPath p) m))
  | .bareCat, none => .error "bare 'cat' with no file and no redirect is not representable"
  | .cmd c, none => .ok (.single c)
  | .cmd c, some (m, p) => .ok (.pipe (.single c) (.single (.write (toPath p) m)))
  | .group g, none => .ok g
  | .group g, some (m, p) => .ok (.pipe g (.single (.write (toPath p) m)))

/-! ## Recursive-descent parser -/

mutual
  private partial def parseSeq (ts : List Tok) : Except String (Pipeline × List Tok) := do
    let (l, ts) ← parseAndOr ts
    parseSeqTail l ts
  private partial def parseSeqTail (l : Pipeline) : List Tok → Except String (Pipeline × List Tok)
    | .seq :: [] => .ok (l, [])            -- trailing `;` is allowed
    | .seq :: ts => do let (r, ts) ← parseAndOr ts; parseSeqTail (.seq l r) ts
    | ts => .ok (l, ts)

  private partial def parseAndOr (ts : List Tok) : Except String (Pipeline × List Tok) := do
    let (l, ts) ← parsePipe ts
    parseAndOrTail l ts
  private partial def parseAndOrTail (l : Pipeline) : List Tok → Except String (Pipeline × List Tok)
    | .andOp :: ts => do let (r, ts) ← parsePipe ts; parseAndOrTail (.andThen l r) ts
    | .orOp :: ts => do let (r, ts) ← parsePipe ts; parseAndOrTail (.orElse l r) ts
    | ts => .ok (l, ts)

  private partial def parsePipe (ts : List Tok) : Except String (Pipeline × List Tok) := do
    let (l, ts) ← parseElem ts
    parsePipeTail l ts
  private partial def parsePipeTail (l : Pipeline) : List Tok → Except String (Pipeline × List Tok)
    | .pipe :: ts => do let (r, ts) ← parseElem ts; parsePipeTail (.pipe l r) ts
    | ts => .ok (l, ts)

  private partial def parseElem (ts : List Tok) : Except String (Pipeline × List Tok) := do
    -- base: either a parenthesized group, or a run of words
    let (base, ts) ← (
      match ts with
      | .lp :: ts => do
          let (g, ts) ← parseSeq ts
          match ts with
          | .rp :: ts => .ok (Base.group g, ts)
          | _ => .error "expected ')'"
      | _ => do
          let (ws, ts) := takeWords ts []
          let b ← wordsToBase ws
          .ok (b, ts))
    -- optional redirect
    match ts with
    | .gt :: .word p :: ts => (applyRedirect base (some (.overwrite, p))).map (·, ts)
    | .gtgt :: .word p :: ts => (applyRedirect base (some (.append, p))).map (·, ts)
    | .gt :: _ | .gtgt :: _ => .error "redirection '>' expects a path"
    | ts => (applyRedirect base none).map (·, ts)

  /-- Consume leading `word` tokens. -/
  private partial def takeWords : List Tok → List String → (List String × List Tok)
    | .word w :: ts, acc => takeWords ts (acc ++ [w])
    | ts, acc => (acc, ts)
end

/-- Parse a bash command string into a `Pipeline`, or an error message. Rejects
anything outside the supported fragment (deny-by-default). -/
partial def parsePipeline (s : String) : Except String Pipeline := do
  let ts ← tokenize s.toList
  if ts.isEmpty then .error "empty command"
  else
    let (p, rest) ← parseSeq ts
    if rest.isEmpty then .ok p
    else .error s!"unexpected trailing tokens ({rest.length} left)"

end ShellWall.Parser
