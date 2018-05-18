/* See LICENSE file for copyright and license details. */

#include <ctype.h>
#include <locale.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <strings.h>
#include <time.h>

#include <X11/Xlib.h>
#include <X11/Xatom.h>
#include <X11/Xutil.h>
#include <X11/Xft/Xft.h>

#include "drw.h"
#include "util.h"
#include "utf8.h"

/* macros TODO: get rid of this */
#define TEXTW(X)              (drw_fontset_getwidth(drw, (X)) + lrpad)

enum {
	SchemeNorm, // normal colorscheme
	SchemeSel,  // selection colorscheme
	SchemeOut,  // I don't really know what this is for
	SchemeCur,  // cursor colorscheme
	SchemeLast,
};

enum {                        // refer to hasharg()
	FuzzyMatchingOpt = 5,     // -F
	OverrideRedirectOpt = 14, // -O
	BottomOfScreenOpt = 33,   // -b
	FastOpt = 37,             // -f
	LineHeightOpt = 39,       // -h
	CaseOpt = 40,             // -i
	LinesOpt = 43,            // -l
	PromptOpt = 47,           // -p
	WidthOpt = 54,            // -w
	XOffsetOpt = 55,          // -x
	YOffsetOpt = 56,          // -y
	CurFgOpt = 102,           // -cc
	NormBgOpt = 111,          // -nb
	SelBgOpt = 116,           // -sb
	NormFgOpt = 119,          // -nf
	SelFgOpt = 124,           // -sf
	FontOpt = 127,            // -fn
};

struct item {
	char *text;
	struct item *left, *right;
	int out;
	double distance;
};

/* function prototypes */
static void fuzzymatch(void);
static void match(void);
static void cleanup(void);
static void calcoffsets(void);
static void drawmenu(void);
static void setup(void);
static void grabfocus(void);
static void grabkeyboard(void);
static void paste(void);
static void readstdin(void);
static void run(void);

static void appenditem(struct item *, struct item **, struct item **);
static void insert(const char *, ssize_t);
static void keypress(XKeyEvent *);

static int drawitem(struct item *, int, int, int);
static int compare_distance(const void *, const void *);
static size_t nextrune(int);

/* global variables */
static char text[BUFSIZ] = "";
static size_t cursor;

static const char *prompt;

static uint_fast16_t menux, menuy, menuw, menuh, menuwusr;
static uint_fast16_t inputw, promptw;
static uint_fast16_t lineh;
static uint_fast16_t lrpad;

static struct item *items;
static struct item *matches, *matchend;
static struct item *prev, *curr, *next, *sel;

static const char worddelimiters[] = " ";

static uint_fast8_t topbar = 1;            // dmenu starts at the top
static uint_fast8_t fast = 0;              // grab keyboard before stdin
static uint_fast8_t override_redirect = 1; // set the override redirect flag
static uint_fast8_t resized = 0;           // dmenu window was already resized
static uint_fast8_t focused = 0;           // dmenu window has focus

static uint_fast16_t lines;                // lines for a vertical listing
static uint_fast16_t linehusr;             // user specified minimum line height

static uint_fast8_t fontcount;             // used when setting fonts manually
static const char *fonts[BUFSIZ] = {       // these are used otherwise
	"DejaVu Sans Mono:size=9",
	"IPAGothic:size=10",
	"Unifont:size=9",
};

static const char *colors[SchemeLast][2] = {
	[SchemeNorm] = { "#000000", "#ffffff" },
	[SchemeSel]  = { "#000000", "#c0c0c0" },
	[SchemeOut]  = { "#000000", "#00ffff" },
	[SchemeCur]  = { "#656565", "#ffffff" },
};

static Display *dpy;
static Window rootW, dmenuW, focusW;
static Atom clipA, utf8A;
static XIC xic;
static int screen;
static int currevert;

static Drw *drw;
static Clr *scheme[SchemeLast];

static int (*fstrncmp)(const char *, const char *, size_t) = strncmp;
static char *(*fstrstr)(const char *, const char *) = strstr;
static void (*fmatch)(void) = fuzzymatch;

static void
appenditem(struct item *item, struct item **list, struct item **last)
{
	if (*last)
		(*last)->right = item;
	else
		*list = item;

	item->left = *last;
	item->right = NULL;
	*last = item;
}

static void
calcoffsets(void)
{
	int i, n;

	if (lines > 0)
		n = lines * lineh;
	else
		n = menuw - (promptw + inputw + TEXTW("<") + TEXTW(">"));
	/* calculate which items will begin the next page and previous page */
	for (i = 0, next = curr; next; next = next->right)
		if ((i += (lines > 0) ? lineh : MIN(TEXTW(next->text), n)) > n)
			break;
	for (i = 0, prev = curr; prev && prev->left; prev = prev->left)
		if ((i += (lines > 0) ? lineh : MIN(TEXTW(prev->left->text), n)) > n)
			break;
}

static void
cleanup(void)
{
	size_t i;

	XUngrabKey(dpy, AnyKey, AnyModifier, rootW);
	for (i = 0; i < SchemeLast; i++)
		free(scheme[i]);
	drw_free(drw);
	XSync(dpy, False);

	/* give focus back to the previously focused window */
	if (override_redirect)
		XSetInputFocus(dpy, focusW, currevert, CurrentTime);

	XCloseDisplay(dpy);
}

static int
drawitem(struct item *item, int x, int y, int w)
{
	if (item == sel)
		drw_setscheme(drw, scheme[SchemeSel]);
	else if (item->out)
		drw_setscheme(drw, scheme[SchemeOut]);
	else
		drw_setscheme(drw, scheme[SchemeNorm]);

	return drw_text(drw, x, y, w, lineh, lrpad / 2, item->text, 0);
}

static void
drawmenu(void)
{
	static char _curbuf[BUFSIZ];
	struct item *item;
	int x = 0, y = 0, fh = drw->fonts->h, w, cx, cw;
	long _utfcp;

	drw_setscheme(drw, scheme[SchemeNorm]);
	drw_rect(drw, 0, 0, menuw, menuh, 1, 1);

	if (prompt && *prompt) {
		drw_setscheme(drw, scheme[SchemeSel]);
		x = drw_text(drw, x, 0, promptw, lineh, lrpad / 2, prompt, 0);
	}

	/* prepare the cursor */
	memset(_curbuf, 0, BUFSIZ);
	if (text[cursor] == '\0')
		_curbuf[0] = '_';
	else
		strncpy(_curbuf, text + cursor, utf8decode(text + cursor, &_utfcp));
	cw = drw_fontset_getwidth(drw, _curbuf);

	memset(_curbuf, 0, BUFSIZ);
	strncpy(_curbuf, text, cursor);
	cx = drw_fontset_getwidth(drw, _curbuf);

	/* draw input field */
	w = (lines > 0 || !matches) ? menuw - x : inputw;
	drw_setscheme(drw, scheme[SchemeNorm]);
	drw_text(drw, x, 0, w, lineh, lrpad / 2, text, 0);

	/* draw cursor */
	drw_setscheme(drw, scheme[SchemeCur]);
	drw_rect(drw, x + cx + lrpad / 2, (lineh - fh)/2, cw, fh,
			text[cursor] == '\0' && focused, 0);

	if (lines > 0) {
		/* draw vertical list */
		for (item = curr; item != next; item = item->right)
			drawitem(item, x, y += lineh, menuw - x);
	} else if (matches) {
		/* draw horizontal list */
		x += inputw;
		w = TEXTW("<");
		if (curr->left) {
			drw_setscheme(drw, scheme[SchemeNorm]);
			drw_text(drw, x, 0, w, lineh, lrpad / 2, "<", 0);
		}
		x += w;
		for (item = curr; item != next; item = item->right)
			x = drawitem(item, x, 0, MIN(TEXTW(item->text), menuw - x - TEXTW(">")));
		if (next) {
			w = TEXTW(">");
			drw_setscheme(drw, scheme[SchemeNorm]);
			drw_text(drw, menuw - w, 0, w, lineh, lrpad / 2, ">", 0);
		}
	}
	drw_map(drw, dmenuW, 0, 0, menuw, menuh);
}

static void
grabfocus(void)
{
	struct timespec ts = { .tv_sec = 0, .tv_nsec = 10000000  };
	Window focuswin;
	int i, revertwin;

	for (i = 0; i < 100; ++i) {
		XGetInputFocus(dpy, &focuswin, &revertwin);
		if (focuswin == dmenuW)
			return;
		XSetInputFocus(dpy, dmenuW, RevertToParent, CurrentTime);
		nanosleep(&ts, NULL);
	}
	die("cannot grab focus");
}

static void
grabkeyboard(void)
{
	struct timespec ts = { .tv_sec = 0, .tv_nsec = 1000000  };
	int i;

	if (!override_redirect)
		return;
	/* try to grab keyboard, we may have to wait for another process to ungrab */
	for (i = 0; i < 1000; i++) {
		if (XGrabKeyboard(dpy, DefaultRootWindow(dpy), True, GrabModeAsync,
		                  GrabModeAsync, CurrentTime) == GrabSuccess)
			return;
		nanosleep(&ts, NULL);
	}
	die("cannot grab keyboard");
}

static int
compare_distance(const void *a, const void *b)
{
	struct item *da = *(struct item **) a;
	struct item *db = *(struct item **) b;

	if (!db)
		return 1;
	if (!da)
		return -1;

	return da->distance == db->distance ? 0 : da->distance < db->distance ? -1 : 1;
}

static void
fuzzymatch(void)
{
	/* bang - we have so much memory */
	struct item *it;
	struct item **fuzzymatches = NULL;
	char c;
	int number_of_matches = 0, i, pidx, sidx, eidx;
	int text_len = strlen(text), itext_len;

	matches = matchend = NULL;

	/* walk through all items */
	for (it = items; it && it->text; it++) {
		if (text_len) {
			itext_len = strlen(it->text);
			pidx = 0; /* pointer */
			sidx = eidx = -1; /* start of match, end of match */
			/* walk through item text */
			for (i = 0; i < itext_len && (c = it->text[i]); i++) {
				/* fuzzy match pattern */
				if (!fstrncmp(&text[pidx], &c, 1)) {
					if(sidx == -1)
						sidx = i;
					pidx++;
					if (pidx == text_len) {
						eidx = i;
						break;
					}
				}
			}
			/* build list of matches */
			if (eidx != -1) {
				/* compute distance */
				/* add penalty if match starts late (log(sidx+2))
				 * add penalty for long a match without many matching characters */
				it->distance = log(sidx + 2) + (double)(eidx - sidx - text_len);
				/* fprintf(stderr, "distance %s %f\n", it->text, it->distance); */
				appenditem(it, &matches, &matchend);
				number_of_matches++;
			}
		} else {
			appenditem(it, &matches, &matchend);
		}
	}

	if (number_of_matches) {
		/* initialize array with matches */
		if (!(fuzzymatches = realloc(fuzzymatches, number_of_matches * sizeof(struct item*))))
			die("cannot realloc %u bytes:", number_of_matches * sizeof(struct item*));
		for (i = 0, it = matches; it && i < number_of_matches; i++, it = it->right) {
			fuzzymatches[i] = it;
		}
		/* sort matches according to distance */
		qsort(fuzzymatches, number_of_matches, sizeof(struct item*), compare_distance);
		/* rebuild list of matches */
		matches = matchend = NULL;
		for (i = 0, it = fuzzymatches[i];  i < number_of_matches && it && \
				it->text; i++, it = fuzzymatches[i]) {
			appenditem(it, &matches, &matchend);
		}
		free(fuzzymatches);
	}
	curr = sel = matches;
	calcoffsets();
}

static void
match(void)
{
	static char **tokv = NULL;
	static int tokn = 0;

	char buf[sizeof text], *s;
	int i, tokc = 0;
	size_t len, textsize;
	struct item *item, *lprefix, *lsubstr, *prefixend, *substrend;

	strcpy(buf, text);
	/* separate input text into tokens to be matched individually */
	for (s = strtok(buf, " "); s; tokv[tokc - 1] = s, s = strtok(NULL, " "))
		if (++tokc > tokn && !(tokv = realloc(tokv, ++tokn * sizeof *tokv)))
			die("cannot realloc %u bytes:", tokn * sizeof *tokv);
	len = tokc ? strlen(tokv[0]) : 0;

	matches = lprefix = lsubstr = matchend = prefixend = substrend = NULL;
	textsize = strlen(text) + 1;
	for (item = items; item && item->text; item++) {
		for (i = 0; i < tokc; i++)
			if (!fstrstr(item->text, tokv[i]))
				break;
		if (i != tokc) /* not all tokens match */
			continue;
		/* exact matches go first, then prefixes, then substrings */
		if (!tokc || !fstrncmp(text, item->text, textsize))
			appenditem(item, &matches, &matchend);
		else if (!fstrncmp(tokv[0], item->text, len))
			appenditem(item, &lprefix, &prefixend);
		else
			appenditem(item, &lsubstr, &substrend);
	}
	if (lprefix) {
		if (matches) {
			matchend->right = lprefix;
			lprefix->left = matchend;
		} else
			matches = lprefix;
		matchend = prefixend;
	}
	if (lsubstr) {
		if (matches) {
			matchend->right = lsubstr;
			lsubstr->left = matchend;
		} else
			matches = lsubstr;
		matchend = substrend;
	}
	curr = sel = matches;
	calcoffsets();
}

static void
insert(const char *str, ssize_t n)
{
	if (strlen(text) + n > sizeof text - 1)
		return;
	/* move existing text out of the way, insert new text, and update cursor */
	memmove(&text[cursor + n], &text[cursor], sizeof text - cursor - MAX(n, 0));
	if (n > 0)
		memcpy(&text[cursor], str, n);
	cursor += n;
	fmatch();
}

static size_t
nextrune(int inc)
{
	ssize_t n;

	/* return location of next utf8 rune in the given direction (+1 or -1) */
	for (n = cursor + inc; n + inc >= 0 && (text[n] & 0xc0) == 0x80; n += inc)
		;
	return n;
}

static void
movewordedge(int dir)
{
	if (dir < 0) { /* move cursor to the start of the word*/
		while (cursor > 0 && strchr(worddelimiters, text[nextrune(-1)]))
			cursor = nextrune(-1);
		while (cursor > 0 && !strchr(worddelimiters, text[nextrune(-1)]))
			cursor = nextrune(-1);
	} else { /* move cursor to the end of the word */
		while (text[cursor] && strchr(worddelimiters, text[cursor]))
			cursor = nextrune(+1);
		while (text[cursor] && !strchr(worddelimiters, text[cursor]))
			cursor = nextrune(+1);
	}
}

static void
keypress(XKeyEvent *ev)
{
	char buf[32];
	int len;
	KeySym ksym;
	Status status;

	len = XmbLookupString(xic, ev, buf, sizeof buf, &ksym, &status);
	switch (status) {
	default: /* XLookupNone, XBufferOverflow */
		return;
	case XLookupChars:
		goto insert;
	case XLookupKeySym:
	case XLookupBoth:
		break;
	}

	if (ev->state & ControlMask) {
		switch(ksym) {
		case XK_a: ksym = XK_Home;      break;
		case XK_b: ksym = XK_Left;      break;
		case XK_c: ksym = XK_Escape;    break;
		case XK_d: ksym = XK_Delete;    break;
		case XK_e: ksym = XK_End;       break;
		case XK_f: ksym = XK_Right;     break;
		case XK_g: ksym = XK_Escape;    break;
		case XK_h: ksym = XK_BackSpace; break;
		case XK_i: ksym = XK_Tab;       break;
		case XK_j: /* fallthrough */
		case XK_J: /* fallthrough */
		case XK_m: /* fallthrough */
		case XK_M: ksym = XK_Return; ev->state &= ~ControlMask; break;
		case XK_n: ksym = XK_Down;      break;
		case XK_p: ksym = XK_Up;        break;

		case XK_k: /* delete right */
			text[cursor] = '\0';
			fmatch();
			break;
		case XK_u: /* delete left */
			insert(NULL, 0 - cursor);
			break;
		case XK_w: /* delete word */
			while (cursor > 0 && strchr(worddelimiters, text[nextrune(-1)]))
				insert(NULL, nextrune(-1) - cursor);
			while (cursor > 0 && !strchr(worddelimiters, text[nextrune(-1)]))
				insert(NULL, nextrune(-1) - cursor);
			break;
		case XK_y: /* paste selection */
		case XK_Y:
			XConvertSelection(dpy, (ev->state & ShiftMask) ? clipA : XA_PRIMARY,
			                  utf8A, utf8A, dmenuW, CurrentTime);
			return;
		case XK_Left:
			movewordedge(-1);
			goto draw;
		case XK_Right:
			movewordedge(+1);
			goto draw;
		case XK_Return:
		case XK_KP_Enter:
			break;
		case XK_bracketleft:
			cleanup();
			exit(1);
		default:
			return;
		}
	} else if (ev->state & Mod1Mask) {
		switch(ksym) {
		case XK_b:
			movewordedge(-1);
			goto draw;
		case XK_f:
			movewordedge(+1);
			goto draw;
		case XK_g: ksym = XK_Home;  break;
		case XK_G: ksym = XK_End;   break;
		case XK_h: ksym = XK_Up;    break;
		case XK_j: ksym = XK_Next;  break;
		case XK_k: ksym = XK_Prior; break;
		case XK_l: ksym = XK_Down;  break;
		default:
			return;
		}
	}

	switch(ksym) {
	default:
insert:
		if (!iscntrl(*buf))
			insert(buf, len);
		break;
	case XK_Delete:
		if (text[cursor] == '\0')
			return;
		cursor = nextrune(+1);
		/* fallthrough */
	case XK_BackSpace:
		if (cursor == 0)
			return;
		insert(NULL, nextrune(-1) - cursor);
		break;
	case XK_End:
		if (text[cursor] != '\0') {
			cursor = strlen(text);
			break;
		}
		if (next) {
			/* jump to end of list and position items in reverse */
			curr = matchend;
			calcoffsets();
			curr = prev;
			calcoffsets();
			while (next && (curr = curr->right))
				calcoffsets();
		}
		sel = matchend;
		break;
	case XK_Escape:
		cleanup();
		exit(1);
	case XK_Home:
		if (sel == matches) {
			cursor = 0;
			break;
		}
		sel = curr = matches;
		calcoffsets();
		break;
	case XK_Left:
		if (cursor > 0 && (!sel || !sel->left || lines > 0)) {
			cursor = nextrune(-1);
			break;
		}
		if (lines > 0)
			return;
		/* fallthrough */
	case XK_Up:
		if (sel && sel->left && (sel = sel->left)->right == curr) {
			curr = prev;
			calcoffsets();
		}
		break;
	case XK_Next:
		if (!next)
			return;
		sel = curr = next;
		calcoffsets();
		break;
	case XK_Prior:
		if (!prev)
			return;
		sel = curr = prev;
		calcoffsets();
		break;
	case XK_Return:
	case XK_KP_Enter:
		puts((sel && !(ev->state & ShiftMask)) ? sel->text : text);
		if (!(ev->state & ControlMask)) {
			cleanup();
			exit(0);
		}
		if (sel)
			sel->out = 1;
		break;
	case XK_Right:
		if (text[cursor] != '\0') {
			cursor = nextrune(+1);
			break;
		}
		if (lines > 0)
			return;
		/* fallthrough */
	case XK_Down:
		if (sel && sel->right && (sel = sel->right) == next) {
			curr = next;
			calcoffsets();
		}
		break;
	case XK_Tab:
		if (!sel)
			return;
		strncpy(text, sel->text, sizeof text - 1);
		text[sizeof text - 1] = '\0';
		cursor = strlen(text);
		fmatch();
		break;
	}

draw:
	drawmenu();
}

static void
paste(void)
{
	char *p, *q;
	int di;
	unsigned long dl;
	Atom da;

	/* we have been given the current selection, now insert it into input */
	if (XGetWindowProperty(dpy, dmenuW, utf8A, 0, (sizeof text / 4) + 1, False,
	                   utf8A, &da, &di, &dl, &dl, (unsigned char **)&p)
	    == Success && p) {
		insert(p, (q = strchr(p, '\n')) ? q - p : (ssize_t)strlen(p));
		XFree(p);
	}
	drawmenu();
}

static void
readstdin(void)
{
	char buf[sizeof text], *p;
	size_t i, imax = 0, size = 0;
	unsigned int tmpmax = 0;

	/* read each line from stdin and add it to the item list */
	for (i = 0; fgets(buf, sizeof buf, stdin); i++) {
		if (i + 1 >= size / sizeof *items)
			if (!(items = realloc(items, (size += BUFSIZ))))
				die("cannot realloc %u bytes:", size);
		if ((p = strchr(buf, '\n')))
			*p = '\0';
		if (!(items[i].text = strdup(buf)))
			die("cannot strdup %u bytes:", strlen(buf) + 1);
		items[i].out = 0;
		drw_font_getexts(drw->fonts, buf, strlen(buf), &tmpmax, NULL);
		if (tmpmax > inputw) {
			inputw = tmpmax;
			imax = i;
		}
	}
	if (items)
		items[i].text = NULL;
	inputw = items ? TEXTW(items[imax].text) : 0;
	lines = MIN(lines, i);
}

static void
run(void)
{
	XEvent ev;

	while (!XNextEvent(dpy, &ev)) {
		if (XFilterEvent(&ev, None))
			continue;
		switch(ev.type) {
		case Expose:
			if (ev.xexpose.count == 0)
				drw_map(drw, dmenuW, 0, 0, menuw, menuh);
			break;
		case FocusOut:
			focused = 0;
			drawmenu();
			break;
		case FocusIn:
			focused = 1;
			drawmenu();
			/* regrab focus from parent window */
			if (ev.xfocus.window != dmenuW)
				grabfocus();
			break;
		case KeyPress:
			keypress(&ev.xkey);
			break;
		case SelectionNotify:
			if (ev.xselection.property == utf8A)
				paste();
			break;
		case VisibilityNotify:
			if (override_redirect && ev.xvisibility.state != VisibilityUnobscured)
				XRaiseWindow(dpy, dmenuW);
			break;
		case ConfigureNotify:
			if (!resized && (ev.xconfigure.width != menuw || ev.xconfigure.height != menuh)) {
				/* attempt to resize window to maintain drw sizes */
				XMoveResizeWindow(dpy, dmenuW,
						ev.xconfigure.x,
						ev.xconfigure.y,
						menuw, menuh);
				resized = 1;
				drawmenu();
			}
			break;
		}
	}
}

static void
setup(void)
{
	int x, y, j;
	XSetWindowAttributes swa;
	XIM xim;
	XWindowAttributes wa;
	XClassHint ch = {"dmenu", "dmenu"};
	XSizeHints *sh = NULL;
	XWMHints wmh = {.flags = InputHint, .input = 1};

	/* init appearance */
	for (j = 0; j < SchemeLast; j++)
		scheme[j] = drw_scm_create(drw, colors[j], 2);

	clipA = XInternAtom(dpy, "CLIPBOARD",   False);
	utf8A = XInternAtom(dpy, "UTF8_STRING", False);

	/* calculate menu geometry */
	lineh = drw->fonts->h + 2;
	lineh = MAX(lineh,linehusr);	/* make a menu line AT LEAST 'linehusr' tall */
	lines = MAX(lines, 0);
	menuh = (lines + 1) * lineh;

	{
		if (!XGetWindowAttributes(dpy, rootW, &wa))
			die("could not get embedding window attributes: 0x%lx",
			    rootW);
		x = menux;
		y = topbar ? menuy : wa.height - menuh - menuy;
		menuw = (menuwusr>0 ? menuwusr : wa.width);
	}

	promptw = (prompt && *prompt) ? TEXTW(prompt) - lrpad / 4 : 0;
	inputw = MIN(inputw, menuw/3);
	fmatch();

	/* create size hints */
	sh = XAllocSizeHints();
	sh->flags = PSize | PMaxSize | PMinSize | PPosition;
	sh->x = x; sh->y = y;
	sh->width = sh->max_width = sh->min_width = menuw;
	sh->height = sh->max_width = sh->min_width = menuh;

	/* create menu window */
	swa.override_redirect = override_redirect ? True : False;
	swa.background_pixel = scheme[SchemeNorm][ColBg].pixel;
	swa.event_mask = StructureNotifyMask | ExposureMask | KeyPressMask |
		VisibilityChangeMask | FocusChangeMask;
	dmenuW = XCreateWindow(dpy, rootW, x, y, menuw, menuh, 0,
	                    CopyFromParent, CopyFromParent, CopyFromParent,
	                    CWOverrideRedirect | CWBackPixel | CWEventMask, &swa);
	XSetClassHint(dpy, dmenuW, &ch);
	XSetWMProperties(dpy, dmenuW, NULL, NULL, NULL, 0, sh, &wmh, &ch);
	XFree(sh);

	/* open input methods */
	xim = XOpenIM(dpy, NULL, NULL, NULL);
	xic = XCreateIC(xim, XNInputStyle, XIMPreeditNothing | XIMStatusNothing,
	                XNClientWindow, dmenuW, XNFocusWindow, dmenuW, NULL);

	XMapRaised(dpy, dmenuW);
	if (override_redirect)
		XSetInputFocus(dpy, dmenuW, RevertToParent, CurrentTime);
	drw_resize(drw, menuw, menuh);
	drawmenu();
}

static uint_fast8_t
hasharg(const char *arg)
{
	uint_fast8_t hash = 0;
	uint_fast8_t i = 0;

	for (; arg[i] != '\0'; ++i)
		hash += (i + 1) * (arg[i] - 'A');

	return hash;
}

int
main(int argc, char *argv[])
{
	XWindowAttributes wa;
	int i;

	for (i = 1; i < argc; ++i) {
		if (argv[i][0] != '-')
			die("not an option");

		switch (hasharg(argv[i] + 1)) {
			case FuzzyMatchingOpt: fmatch = match; break;
			case OverrideRedirectOpt: override_redirect = 0; break;
			case BottomOfScreenOpt: topbar = 0; break;
			case FastOpt: fast = 1; break;
			case LinesOpt: lines = atoi(argv[++i]); break;
			case PromptOpt: prompt = argv[++i]; break;
			case WidthOpt: menuwusr = atoi(argv[++i]); break;
			case XOffsetOpt: menux = atoi(argv[++i]); break;
			case YOffsetOpt: menuy = atoi(argv[++i]); break;
			case CurFgOpt: colors[SchemeCur][ColFg] = argv[++i]; break;
			case NormBgOpt: colors[SchemeNorm][ColBg] = argv[++i]; break;
			case NormFgOpt: colors[SchemeNorm][ColFg] = argv[++i]; break;
			case SelBgOpt: colors[SchemeSel][ColBg] = argv[++i]; break;
			case SelFgOpt: colors[SchemeSel][ColFg] = argv[++i]; break;
			case FontOpt: fonts[fontcount++] = argv[++i]; break;
			case CaseOpt: fstrncmp = strncasecmp; fstrstr = cistrstr; break;
			case LineHeightOpt:
				linehusr = atoi(argv[++i]);
				linehusr = MAX(linehusr,8);
				break;
			default:
				die("bad option: %s", argv[i]);
		}
	}

	if (!setlocale(LC_CTYPE, "") || !XSupportsLocale())
		fputs("warning: no locale support\n", stderr);
	if (!XSetLocaleModifiers(""))
		fputs("warning: no locale modifiers support\n", stderr);
	if (!(dpy = XOpenDisplay(NULL)))
		die("cannot open display");

	screen = DefaultScreen(dpy);
	rootW = RootWindow(dpy, screen);

	if (!XGetWindowAttributes(dpy, rootW, &wa))
		die("could not get embedding window attributes: 0x%lx",
		    rootW);

	drw = drw_create(dpy, screen, rootW, wa.width, wa.height);

	if (!drw_fontset_create(drw, fonts, (fontcount > 0 ? fontcount : 3)))
		die("no fonts could be loaded.");

	lrpad = drw->fonts->h;

	/* focus mangling when override_redirect is set */
	if (override_redirect)
		XGetInputFocus(dpy, &focusW, &currevert);

	if (fast) {
		grabkeyboard();
		readstdin();
	} else {
		readstdin();
		grabkeyboard();
	}
	setup();
	run();

	return 1; /* unreachable */
}

// vim: set tabstop=4 shiftwidth=4 :
