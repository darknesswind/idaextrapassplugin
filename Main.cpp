
#include "stdafx.h"
#include <WaitBoxEx.h>
#include <SegSelect.h>
#include <IdaOgg.h>
#include <unordered_set>
#include <vector>

#include "complete_ogg.h"

//#define VBDEV
//#define LOG_FILE

// Count of eSTATE_PASS_1 unknown byte gather passes
#define UNKNOWN_PASSES 8

// x86 hack for speed in alignment value searching
// Defs from IDA headers, not supposed to be exported but need to because some cases not covered
// by SDK accessors, etc.
#define MS_VAL  0x000000FFLU	// Mask for byte value
#define FF_IVL  0x00000100LU	// Byte has value ?
#define FF_REF  0x00001000LU	// has references
#define FF_0OFF 0x00500000LU	// Offset?

/*
    1st pass. Look for " dd " without "offset". Finds missing code
    For each found:
        1. Find the extents of the block and undefine it
        2. Analise it for code

    2nd pass. Look for " dw " without "offset". Finds missing code
    Same as above.

    3nd pass. Look for " db " without "offset". Finds missing code
    Same as above.

    4th pass. Look at gaps between functions. Finds missing functions
    If code is found try to make a function of it.
*/


// Process states
enum eSTATES
{
    eSTATE_INIT,	// Initialize
	eSTATE_START,	// Start processing

    eSTATE_PASS_1,	// Find unknown data in code space
    eSTATE_PASS_2,	// Find missing "align" blocks
	eSTATE_PASS_3,	// Find lost code instructions
	eSTATE_PASS_4,  // Find missing functions part

    eSTATE_FINISH,  // Done

    eSTATE_EXIT,
};

static const char SITE_URL[] = { "http://www.macromonkey.com/bb/index.php/topic,21.0.html" };

// UI options bit flags
// *** Must be same sequence as check box options
const static WORD OPT_DATATOBYTES = (1 << 0);
const static WORD OPT_ALIGNBLOCKS = (1 << 1);
const static WORD OPT_MISSINGCODE = (1 << 2);
const static WORD OPT_MISSINGFUNC = (1 << 3);

// Function info container
struct FUNCNODE
{
	ea_t address;
	UINT size;
};

typedef std::unordered_set<ea_t> ADDRSET;
typedef std::vector<FUNCNODE> FUNCLIST;

// === Function Prototypes ===
static void showEndStats();
static void nextState();
static void processFuncGap(ea_t start, UINT size);
static bool idaapi isAlignByte(flags_t flags, void *ud);
static bool idaapi isData(flags_t flags, void *ud);

// === Data ===
static TIMESTAMP s_startTime = 0, s_stepTime = 0;
static segment_t *s_thisSeg  = NULL;
static ea_t s_segStart       = NULL;
static ea_t s_segEnd         = NULL;
static ea_t s_currentAddress = NULL;
static ea_t s_lastAddress    = NULL;
static BOOL s_isBreak        = FALSE;
#ifdef LOG_FILE
static FILE *s_logFile       = NULL;
#endif
static eSTATES s_state       = eSTATE_INIT;
static int  s_startFuncCount = 0;
static int  s_pass1Loops     = 0;
static UINT s_funcCount      = 0;
static UINT s_funcIndex      = 0;
//
static UINT s_unknownDataCount = 0;
static UINT s_alignFixes       = 0;
static UINT s_codeFixes        = 0;
//
static BOOL s_doDataToBytes  = TRUE;
static BOOL s_doAlignBlocks  = TRUE;
static BOOL s_doMissingCode  = TRUE;
static BOOL s_doMissingFunc  = TRUE;
static WORD s_audioAlertWhenDone = 1;
static SegSelect::segments *chosen = NULL;


// Options dialog
static const char optionDialog[] =
{
	"BUTTON YES* Continue\n" // 'Continue' instead of 'okay'

	// Help body
	"HELP\n"
	"\"ExtraPass PlugIn\""
	"An IDA Pro Win32 x86 executable clean up plugin, by Sirmabus\n\n"

	"This plugin does an \"extra pass\" to help fix and cleanup the IDB.\n"
	"It can find tens of thousands missing functions and alignment blocks making\n"
	"your IDB more complete and easier to reverse.\n\n"

	"It actually does essentially five processing steps:\n"
	"1. Convert stray code section values to \"unknown\".\n"
	"2. Fix missing \"align\" blocks.\n"
	"3. Fix missing code bytes.\n"
	"4. Locate and fix missing/undefined functions.\n\n"

	"It's intended for, and only tested on typical MSVC and Intel complied Windows\n"
	"32bit binary executables but it might still be helpful on Delphi/Borland and\n"
	"other complied targets.\n"
	"For best results, run the plugin at least two times.\n"
	"Will not work well with Borland(r) and other targets that has data mixed with code in the same space.\n"
	"See \"ExtraPass.txt\" for more help.\n\n"
	"Forum: http://www.macromonkey.com/bb/\n"
	"ENDHELP\n"

	// Title
	"ExtraPass Plugin\n"

	// Message text
	"Version %Aby Sirmabus\n"
    "<#Click to open site.#www.macromonkey.com:k:2:1::>\n\n"

	"Choose processing steps:\n"

	// checkbox -> s_wDoDataToBytes
	"<#Scan the entire code section converting all unknown DD,DW,DB data declarations to\n"
	"unknown bytes, to be reexamined as possible code, functions, and alignment blocks\n"
	"in the following passes.#1 Convert unknown data.                                     :C>\n"

	// checkbox -> s_wDoAlignBlocks
	"<#Fix missing \"align xx\" blocks.#2 Fix align blocks.:C>\n"

	// checkbox -> s_wDoMissingCode
	"<#Fix lost code instructions.#3 Fix missing code.:C>\n"

	// checkbox -> s_wDoMissingFunc
	"<#Fix missing/undeclared functions.#4 Fix missing functions.:C>>\n"

	// checkbox -> s_wAudioAlertWhenDone
	"<#Play sound on completion.#Play sound on completion.                                     :C>>\n"


	"<#Choose the code segment(s) to process.\nElse will use the first CODE segment by default.\n#Choose Code Segments:B:1:8::>\n"
    "                      "
};

// Checks and handles if break key pressed; returns TRUE on break.
static BOOL checkBreak()
{
    if (!s_isBreak)
    {
        if (WaitBox::isUpdateTime())
        {
            if (WaitBox::updateAndCancelCheck())
            {
                msg("\n*** Aborted ***\n\n");

                // Show stats then directly to exit
                showEndStats();
                s_state = eSTATE_EXIT;
                s_isBreak = TRUE;
                return(TRUE);
            }
        }
    }
    return(s_isBreak);
}

// Make and address range "unknown" so it can be set with something else
static void makeUnknown(ea_t start, ea_t end)
{
   autoWait();
    //auto_mark_range(s_currentAddress, end, AU_UNK);
    //do_unknown(start, (DOUNK_SIMPLE | DOUNK_NOTRUNC));

    do_unknown_range(start, (end - start), (DOUNK_SIMPLE | DOUNK_NOTRUNC));
    autoWait();
}

// Initialize
int idaapi plugin_init()
{
	// Only Intel x86/AMD64 supported
	if (ph.id != PLFM_386)
		return(PLUGIN_SKIP);

    s_state = eSTATE_INIT;
	return(PLUGIN_OK);
}

// Uninitialize
void idaapi plugin_exit()
{
    try
    {
        #ifdef LOG_FILE
        if(s_logFile)
        {
            qfclose(s_logFile);
            s_logFile = NULL;
        }
        #endif

        if (chosen)
        {
            SegSelect::free(chosen);
            chosen = NULL;
        }

        OggPlay::endPlay();
        set_user_defined_prefix(0, NULL);
    }
    CATCH()
}

// Handler for choose code and data segment buttons
static void idaapi chooseBtnHandler(TView *fields[], int code)
{
    if (chosen = SegSelect::select(SegSelect::CODE_HINT, "Choose code segments"))
    {
        msg("Chosen: ");
        for (SegSelect::segments::iterator it = chosen->begin(); it != chosen->end(); ++it)
        {
            char buffer[64];
            if (get_true_segm_name(*it, buffer, SIZESTR(buffer)) <= 0)
                strcpy(buffer, "????");

            SegSelect::segments::iterator it2 = it; ++it2;
            if (it2 != chosen->end())
                msg("\"%s\", ", buffer);
            else
                msg("\"%s\"", buffer);
        }
        msg("\n");
        WaitBox::processIdaEvents();
    }
}

static void idaapi doHyperlink(TView *fields[], int code) { open_url(SITE_URL); }


// Plug-in process
void idaapi plugin_run(int arg)
{
    try
    {
        while (TRUE)
        {
            switch (s_state)
            {
                // Initialize
                case eSTATE_INIT:
                {
					char version[16];
					sprintf(version, "%u.%u", HIBYTE(MY_VERSION), LOBYTE(MY_VERSION));
					msg("\n>> ExtraPass: v: %s, BD: %s, By Sirmabus ==\n", version, __DATE__);
					refreshUI();
                    WaitBox::processIdaEvents();
                    s_isBreak = FALSE;

                    // Do UI for process pass selection
                    s_doDataToBytes = s_doAlignBlocks = s_doMissingCode = s_doMissingFunc = TRUE;
                    s_audioAlertWhenDone = TRUE;

                    WORD optionFlags = 0;
                    if (s_doDataToBytes) optionFlags |= OPT_DATATOBYTES;
                    if (s_doAlignBlocks) optionFlags |= OPT_ALIGNBLOCKS;
                    if (s_doMissingCode) optionFlags |= OPT_MISSINGCODE;
                    if (s_doMissingFunc) optionFlags |= OPT_MISSINGFUNC;

                    {
                        // To add forum URL to help box
                        int result = AskUsingForm_c(optionDialog, version, doHyperlink, &optionFlags, &s_audioAlertWhenDone, chooseBtnHandler);
                        if (!result || (optionFlags == 0))
                        {
                            // User canceled, or no options selected, bail out
                            msg(" - Canceled -\n\n");
                            WaitBox::processIdaEvents();
                            s_state = eSTATE_EXIT;
                            break;
                        }

                        s_doDataToBytes = ((optionFlags & OPT_DATATOBYTES) != 0);
                        s_doAlignBlocks = ((optionFlags & OPT_ALIGNBLOCKS) != 0);
                        s_doMissingCode = ((optionFlags & OPT_MISSINGCODE) != 0);
                        s_doMissingFunc = ((optionFlags & OPT_MISSINGFUNC) != 0);
                    }

                    // IDA must be IDLE
                    if (autoIsOk())
                    {
                        // Ask for the log file name once
                        #ifdef LOG_FILE
                        if(!s_logFile)
                        {
                            if(char *szFileName = askfile_c(1, "*.txt", "Select a log file name:"))
                            {
                                // Open it for appending
                                s_logFile = qfopen(szFileName, "ab");
                            }
                        }
                        if(!s_logFile)
                        {
                            msg("** Log file open failed! Aborted. **\n");
                            return;
                        }
                        #endif

                        s_thisSeg = NULL;
                        s_unknownDataCount = 0;
                        s_alignFixes = s_codeFixes = 0;
                        s_pass1Loops = 0; s_funcIndex = 0;
                        s_startFuncCount = get_func_qty();

                        if (s_startFuncCount > 0)
                        {
                            char buffer[32];
                            msg("Starting function count: %s\n", prettyNumberString(s_startFuncCount, buffer));
                            WaitBox::processIdaEvents();

                            /*
                            msg("\n=========== Segments ===========\n");
                            int iSegCount = get_segm_qty();
                            for(int i = 0; i < iSegCount; i++)
                            {
                                if(segment_t *pSegInfo = getnseg(i))
                                {
                                char szName[128] = {0};
                                get_segm_name(pSegInfo, szName, (sizeof(szName) - 1));
                                char szClass[16] = {0};
                                get_segm_class(pSegInfo, szClass, (sizeof(szClass) - 1));
                                msg("[%d] \"%s\", \"%s\".\n", i, szName, szClass);
                                }
                            }
                            */

                            // First chosen seg
                            if (chosen && !chosen->empty())
                            {
                                s_thisSeg = chosen->back();
                                chosen->pop_back();
                            }
                            else
                            // Use the first CODE seg
                            {
                                int iSegCount = get_segm_qty();
                                int iIndex = 0;
                                for (; iIndex < iSegCount; iIndex++)
                                {
                                    if (s_thisSeg = getnseg(iIndex))
                                    {
                                        char sclass[32];
                                        if (get_segm_class(s_thisSeg, sclass, SIZESTR(sclass)) <= 0)
                                            break;
                                        else
                                        if (strcmp(sclass, "CODE") == 0)
                                            break;
                                    }
                                }

                                if (iIndex >= iSegCount)
                                    s_thisSeg = NULL;
                            }

                            if (s_thisSeg)
                            {
                                WaitBox::show();
                                WaitBox::updateAndCancelCheck(-1);
                                s_segStart = s_thisSeg->startEA;
                                s_segEnd   = s_thisSeg->endEA;
                                nextState();
                                break;
                            }
                            else
                                msg("** No code segment found to process! **\n*** Aborted ***\n\n");
                        }
                        else
                            msg("** No functions in DB?! **\n*** Aborted ***\n\n");
                    }
                    else
                        msg("** Wait for IDA to finish processing before starting plugin! **\n*** Aborted ***\n\n");

                    // Canceled or error'ed, bail out
                    s_state = eSTATE_EXIT;
                }
                break;

                // Start up process
                case eSTATE_START:
                {
                    s_currentAddress = 0;

                    char name[64];
                    if (get_true_segm_name(s_thisSeg, name, SIZESTR(name)) <= 0)
                        strcpy(name, "????");
                    char sclass[32];
                    if(get_segm_class(s_thisSeg, sclass, SIZESTR(sclass)) <= 0)
                        strcpy(sclass, "????");
                    msg("\nProcessing segment: \"%s\", type: %s, address: " EAFORMAT "-" EAFORMAT ", size: %08X\n\n", name, sclass, s_thisSeg->startEA, s_thisSeg->endEA, s_thisSeg->size());

                    // Move to first process state
                    s_startTime = getTimeStamp();
                    nextState();
                }
                break;


                // Find unknown data values in code
                //#define PASS1_DEBUG
                case eSTATE_PASS_1:
                {
                    if (s_currentAddress < s_segEnd)
                    {
                        // Value at this location data?
                        autoWait();
                        flags_t flags = get_flags_novalue(s_currentAddress);
                        if (isData(flags) && !isAlign(flags))
                        {
                            #ifdef PASS1_DEBUG
                            msg(EAFORMAT",  F: %08X data\n", s_currentAddress, flags);
                            #endif
                            ea_t end = next_head(s_currentAddress, s_segEnd);

                            // Handle an occasional over run case
                            if (end == BADADDR)
                            {
                                #ifdef PASS1_DEBUG
                                msg(EAFORMAT" **** abort end\n", s_currentAddress);
                                #endif
                                s_currentAddress = (s_segEnd - 1);
                                break;
                            }

                            // Skip if it has offset reference (most common occurrence)
                            BOOL bSkip = FALSE;
                            if (flags & FF_0OFF)
                            {
                                #ifdef PASS1_DEBUG
                                msg("  skip offset.\n");
                                #endif
                                bSkip = TRUE;
                            }
                            else
                            // Has a reference?
                            if (flags & FF_REF)
                            {
                                ea_t eaDRef = get_first_dref_to(s_currentAddress);
                                if (eaDRef != BADADDR)
                                {
                                    // Ref part an offset?
                                    flags_t flags2 = get_flags_novalue(eaDRef);
                                    if (isCode(flags2) && isOff1(flags2))
                                    {
                                        // Decide instruction to global "cmd" struct
                                        BOOL bIsByteAccess = FALSE;
                                        if (decode_insn(eaDRef))
                                        {
                                            switch (cmd.itype)
                                            {
                                                // movxx style move a byte?
                                                case NN_movzx:
                                                case NN_movsx:
                                                {
                                                    #ifdef PASS1_DEBUG
                                                    msg(EAFORMAT" movzx\n", s_currentAddress);
                                                    #endif
                                                    bIsByteAccess = TRUE;
                                                }
                                                break;

                                                case NN_mov:
                                                {
                                                    if ((cmd.Operands[0].type == o_reg) && (cmd.Operands[1].dtyp == dt_byte))
                                                    {
                                                        #ifdef PASS1_DEBUG
                                                        msg(EAFORMAT" mov\n", s_currentAddress);
                                                        #endif
                                                        /*
                                                        msg(" [0] T: %d, D: %d, \n", cmd.Operands[0].type, cmd.Operands[0].dtyp);
                                                        msg(" [1] T: %d, D: %d, \n", cmd.Operands[1].type, cmd.Operands[1].dtyp);
                                                        msg(" [2] T: %d, D: %d, \n", cmd.Operands[2].type, cmd.Operands[2].dtyp);
                                                        msg(" [3] T: %d, D: %d, \n", cmd.Operands[3].type, cmd.Operands[3].dtyp);
                                                        */
                                                        bIsByteAccess = TRUE;
                                                    }
                                                }
                                                break;
                                            };
                                        }

                                        // If it's byte access, assume it's a byte switch table
                                        if (bIsByteAccess)
                                        {
                                            #ifdef PASS1_DEBUG
                                            msg(EAFORMAT" not byte\n", s_currentAddress);
                                            #endif
                                            makeUnknown(s_currentAddress, end);
                                            // Step through making the array, and any bad size a byte
                                            //for(ea_t i = s_eaCurrentAddress; i < eaEnd; i++){ doByte(i, 1); }
                                            doByte(s_currentAddress, (end - s_currentAddress));
                                            autoWait();
                                            bSkip = TRUE;
                                        }
                                    }
                                }
                            }

                            // Make it unknown bytes
                            if (!bSkip)
                            {
                                #ifdef PASS1_DEBUG
                                msg(EAFORMAT" "EAFORMAT" %02X unknown\n", s_currentAddress, end, get_flags_novalue(s_currentAddress));
                                #endif
                                makeUnknown(s_currentAddress, end);
                                s_unknownDataCount++;

                                // Note: Might have triggered auto-analysis and a alignment or function could be here now
                            }

                            // Advance to next data value, or the end which ever comes first
                            s_currentAddress = end;
                            if (s_currentAddress < s_segEnd)
                            {
                                s_currentAddress = nextthat(s_currentAddress, s_segEnd, isData, NULL);
                                break;
                            }
                        }
                        else
                        {
                            // Advance to next data value, or the end which ever comes first
                            s_currentAddress = nextthat(s_currentAddress, s_segEnd, isData, NULL);
                            break;
                        }
                    }

                    if (++s_pass1Loops < UNKNOWN_PASSES)
                    {
                        #ifdef PASS1_DEBUG
                        msg("** Pass %d Unknowns: %u\n", s_pass1Loops, s_unknownDataCount);
                        #endif
                        s_currentAddress = s_lastAddress = s_segStart;
                    }
                    else
                    {
                        #ifdef PASS1_DEBUG
                        msg("** Pass %d Unknowns: %u\n", s_pass1Loops, s_unknownDataCount);
                        #endif
                        nextState();
                    }
                }
                break;  // Find unknown data values in code


                // Find missing align blocks
                //#define PASS2_DEBUG
                case eSTATE_PASS_2:
                {
                    #define NEXT(_Here, _Limit) nextthat(_Here, _Limit, isAlignByte, NULL)

                    // Still inside this code segment?
                    ea_t end = s_segEnd;
                    if (s_currentAddress < end)
                    {
                        // Look for next unknown alignment type byte
                        // Will return BADADDR if none found which will catch in the endEA test
                        flags_t flags = getFlags(s_currentAddress);
                        if (!isAlignByte(flags, NULL))
                            s_currentAddress = NEXT(s_currentAddress, s_segEnd);
                        if (s_currentAddress < end)
                        {
                            // Catch when we get caught up in an array, etc.
                            ea_t startAddress = s_currentAddress;
                            if (s_currentAddress <= s_lastAddress)
                            {
                                // Move to next header and try again..
                                #ifdef PASS2_DEBUG
                                //msg(EAFORMAT", F: 0x%X *** Align test in array #1 ***\n", s_currentAddress, flags);
                                #endif
                                s_currentAddress = s_lastAddress = nextaddr(s_currentAddress);
                                break;
                            }

                            #ifdef PASS2_DEBUG
                            //msg(EAFORMAT" Start.\n", startAddress);
                            //msg(EAFORMAT", F: %08X.\n", startAddress, get_flags_novalue(startAddress));
                            #endif
                            s_lastAddress = s_currentAddress;

                            // Get run count of this align byte
                            UINT alignByteCount = 1;
                            BYTE startAlignValue = get_byte(startAddress);

                            while (TRUE)
                            {
                                // Next byte
                                s_currentAddress = nextaddr(s_currentAddress);
                                #ifdef PASS2_DEBUG
                                //msg(EAFORMAT" Next.\n", s_currentAddress);
                                //msg(EAFORMAT", F: %08X.\n", s_currentAddress, get_flags_novalue(s_currentAddress));
                                #endif

                                if (s_currentAddress < end)
                                {
                                    // Catch when we get caught up in an array, etc.
                                    if (s_currentAddress <= s_lastAddress)
                                    {
                                        #ifdef PASS2_DEBUG
                                        //msg(EAFORMAT", F: %08X *** Align test in array #2 ***\n", startAddress, get_flags_novalue(s_currentAddress));
                                        #endif
                                        s_currentAddress = s_lastAddress = nextaddr(s_currentAddress);
                                        break;
                                    }
                                    s_lastAddress = s_currentAddress;

                                    // Count if it' still the same byte
                                    if (get_byte(s_currentAddress) == startAlignValue)
                                        alignByteCount++;
                                    else
                                        break;
                                }
                                else
                                    break;
                            };

                            // Do these bytes bring about at least a 16 (could be 32) align?
                            // TODO: Must we consider other alignments such as 4 and 8?
                            //       Probably a compiler option that is not normally used anymore.
                            if (((startAddress + alignByteCount) & (16 - 1)) == 0)
                            {
                                // If short count, only try alignment if the line above or a below us has n xref
                                // We don't want to try to align odd code and switch table bytes, etc.
                                if (alignByteCount <= 2)
                                {
                                    BOOL hasRef = FALSE;

                                    // Before us
                                    ea_t endAddress = (startAddress + alignByteCount);
                                    ea_t ref = get_first_cref_from(endAddress);
                                    if (ref != BADADDR)
                                    {
                                        //msg(EAFORMAT " cref from end.\n", endAddress);
                                        hasRef = TRUE;
                                    }
                                    else
                                    {
                                        ref = get_first_cref_to(endAddress);
                                        if (ref != BADADDR)
                                        {
                                            //msg(EAFORMAT " cref to end.\n", endAddress);
                                            hasRef = TRUE;
                                        }
                                    }

                                    // After us
                                    if (ref == BADADDR)
                                    {
                                        ea_t foreAddress = (startAddress - 1);
                                        ref = get_first_cref_from(foreAddress);
                                        if (ref != BADADDR)
                                        {
                                            //msg(EAFORMAT " cref from start.\n", eaForeAddress);
                                            hasRef = TRUE;
                                        }
                                        else
                                        {
                                            ref = get_first_cref_to(foreAddress);
                                            if (ref != BADADDR)
                                            {
                                                //msg(EAFORMAT " cref to start.\n", eaForeAddress);
                                                hasRef = TRUE;
                                            }
                                        }
                                    }

                                    // No code ref, now look for a broken code ref
                                    if (ref == BADADDR)
                                    {
                                        // This is still not complete as it could still be code, but pointing to a vftable
                                        // entry in data.
                                        // But should be fixed on more passes.
                                        ea_t endAddress = (startAddress + alignByteCount);
                                        ref = get_first_dref_from(endAddress);
                                        if (ref != BADADDR)
                                        {
                                            // If it the ref points to code assume code is just broken here
                                            if (isCode(get_flags_novalue(ref)))
                                            {
                                                //msg(EAFORMAT " dref from end %08X.\n", eaRef, eaEndAddress);
                                                hasRef = TRUE;
                                            }
                                        }
                                        else
                                        {
                                            ref = get_first_dref_to(endAddress);
                                            if (ref != BADADDR)
                                            {
                                                if (isCode(get_flags_novalue(ref)))
                                                {
                                                    //msg(EAFORMAT " dref to end %08X.\n", eaRef, eaEndAddress);
                                                    hasRef = TRUE;
                                                }
                                            }
                                        }

                                        if (ref == BADADDR)
                                        {
                                            //msg(EAFORMAT " NO REF.\n", eaStartAddress);
                                        }
                                    }

                                    // Assume it's not an alignment byte(s) and bail out
                                    if (!hasRef) break;
                                }

                                // If it's not an align make block already try to fix it
								flags_t flags = get_flags_novalue(startAddress);
								UINT itemSize = get_item_size(startAddress);
								if (!isAlign(flags) || (itemSize != alignByteCount))
								{
									makeUnknown(startAddress, ((startAddress + alignByteCount) - 1));
									BOOL result = doAlign(startAddress, alignByteCount, 0);
									autoWait();
									#ifdef PASS2_DEBUG
									msg(EAFORMAT" %d %d  %d %d %d DO ALIGN.\n", startAddress, alignByteCount, result, isAlign(flags), itemSize, get_item_size(startAddress));
									#endif
									if (result)
									{
										#ifdef PASS2_DEBUG
										//msg(EAFORMAT" %d ALIGN.\n", startAddress, alignByteCount);
										#endif
										s_alignFixes++;
									}
									else
									{
										// There are cases were IDA will fail even when the alignment block is obvious.
										// Usually when it's an ALIGN(32) and there is a run of 16 align bytes
										// Could at least do a code analyze on it. Then IDA will at least make a mini array of it
										#ifdef PASS2_DEBUG
										msg(EAFORMAT" %d ALIGN FAIL ***\n", startAddress, alignByteCount);
										//s_alignFails++;
										#endif
									}
								}
                            }
                        }

                        break;
                    }

                    s_currentAddress = s_segEnd;
                    nextState();
                    #undef NEXT
                }
                break; // Find missing align blocks


                // Find missing code
                //#define PASS3_DEBUG
                case eSTATE_PASS_3:
                {
                    // Still inside segment?
                    if (s_currentAddress < s_segEnd)
                    {
                        // Look for next unknown value
                        ea_t startAddress = next_unknown(s_currentAddress, s_segEnd);
                        if (startAddress < s_segEnd)
                        {
                            s_currentAddress = startAddress;
                            //s_uStrayBYTE++;
                            //msg(EAFORMAT " unknown.\n");

                            // Catch when we get caught up in an array, etc.
                            if (s_currentAddress <= s_lastAddress)
                            {
                                // Move to next header and try again..
                                s_currentAddress = next_unknown(s_currentAddress, s_segEnd);
                                s_lastAddress = s_currentAddress;
                                break;
                            }
                            s_lastAddress = s_currentAddress;

                            // Try to make code of it
                            autoWait();
                            int result = create_insn(s_currentAddress);
                            autoWait();
                            #ifdef PASS3_DEBUG
                            msg(EAFORMAT" DO CODE %d\n", s_currentAddress, result);
                            #endif
                            if(result > 0)
                                s_codeFixes++;
                            else
                            {
                                #ifdef PASS3_DEBUG
                                msg(EAFORMAT" fix fail.\n", s_currentAddress);
                                #endif
                            }

                            // Start from possible next byte
                            s_currentAddress++;
                            break;
                        }
                    }

                    // Next state
                    s_currentAddress = s_segEnd;
                    nextState();
                }
                break; // End: Find missing code


                // Discover missing functions part 1
                case eSTATE_PASS_4:
                {
                    if (s_funcIndex < s_funcCount)
                    {
                        // Get function gap from the bottom of the function to the start of the next
                        func_t *f1 = getn_func(s_funcIndex + 0);
                        func_t *f2 = getn_func(s_funcIndex + 1);

                        UINT gapSize = (f2->startEA - f1->endEA);
                        if (gapSize > 0)
                            processFuncGap(f1->endEA, gapSize);

                        s_funcIndex++;
                    }
                    else
                    {
                        s_currentAddress = s_segEnd;
                        nextState();
                    }
                }
                break;


                // Finished processing
                case eSTATE_FINISH:
                {
                    nextState();
                }
                break;

                // Done processing
                case eSTATE_EXIT:
                {
					WaitBox::hide();
                    nextState();
                    goto BailOut;
                }
                break;
            };

            // Check & bail out on 'break' press
			if (checkBreak())
			{
				WaitBox::hide();
				goto BailOut;
			}
        };

        BailOut:;
    }
    CATCH()
}


// Do next state logic
static void nextState()
{
	// Rewind
	if(s_state < eSTATE_FINISH)
	{
		// Top of code seg
		s_currentAddress = s_lastAddress = s_segStart;
		//SafeJumpTo(s_uCurrentAddress);
		autoWait();
	}

	// Logic
	switch(s_state)
	{
		// Init
		case eSTATE_INIT:
		{
			s_state = eSTATE_START;
		}
		break;

		// Start
		case eSTATE_START:
		{
			if(s_doDataToBytes)
			{
				msg("===== Fixing bad code bytes =====\n");
				s_stepTime = getTimeStamp();
				s_state = eSTATE_PASS_1;
			}
			else
			if(s_doAlignBlocks)
			{
				msg("===== Missing align blocks =====\n");
				s_stepTime = getTimeStamp();
				s_state = eSTATE_PASS_2;
			}
			else
			if(s_doMissingCode)
			{
				msg("===== Missing code =====\n");
				s_stepTime = getTimeStamp();
				s_state = eSTATE_PASS_3;
			}
			else
			if(s_doMissingFunc)
			{
				msg("===== Missing functions =====\n");
                WaitBox::processIdaEvents();
				s_stepTime = getTimeStamp();
                s_funcIndex = 0;
                s_funcCount = (get_func_qty() - 1);
				s_state = eSTATE_PASS_4;
			}
			else
				s_state = eSTATE_FINISH;

            WaitBox::processIdaEvents();
		}
		break;

		// Find unknown data in code space
		case eSTATE_PASS_1:
		{
			msg("Time: %s.\n\n", timeString(getTimeStamp() - s_stepTime));

			if(s_doAlignBlocks)
			{
				msg("===== Missing align blocks =====\n");
				s_stepTime = getTimeStamp();
				s_state = eSTATE_PASS_2;
			}
			else
			if(s_doMissingCode)
			{
				msg("===== Missing code =====\n");
				s_stepTime = getTimeStamp();
				s_state = eSTATE_PASS_3;
			}
			else
			if(s_doMissingFunc)
			{
				msg("===== Missing functions =====\n");
                WaitBox::processIdaEvents();
				s_stepTime = getTimeStamp();
                s_funcIndex = 0;
                s_funcCount = (get_func_qty() - 1);
				s_state = eSTATE_PASS_4;
			}
			else
				s_state = eSTATE_FINISH;

            WaitBox::processIdaEvents();
		}
		break;


		// From missing align block pass
		case eSTATE_PASS_2:
		{
			msg("Time: %s.\n\n", timeString(getTimeStamp() - s_stepTime));

			if(s_doMissingCode)
			{
				msg("===== Missing code =====\n");
				s_stepTime = getTimeStamp();
				s_state = eSTATE_PASS_3;
			}
			else
			if(s_doMissingFunc)
			{
				msg("===== Missing functions =====\n");
                WaitBox::processIdaEvents();
				s_stepTime = getTimeStamp();
                s_funcIndex = 0;
                s_funcCount = (get_func_qty() - 1);
				s_state = eSTATE_PASS_4;
			}
			else
				s_state = eSTATE_FINISH;

            WaitBox::processIdaEvents();
		}
		break;

		// From missing code pass
		case eSTATE_PASS_3:
		{
			msg("Time: %s.\n\n", timeString(getTimeStamp() - s_stepTime));

			if(s_doMissingFunc)
			{
				msg("===== Missing functions =====\n");
                WaitBox::processIdaEvents();
				s_stepTime = getTimeStamp();
                s_funcIndex = 0;
                s_funcCount = (get_func_qty() - 1);
				s_state = eSTATE_PASS_4;
			}
			else
				s_state = eSTATE_FINISH;

            WaitBox::processIdaEvents();
		}
		break;

		// From missing function pass part
		case eSTATE_PASS_4:
		{
			msg("Time: %s.\n\n", timeString(getTimeStamp() - s_stepTime));
			s_state = eSTATE_FINISH;

            WaitBox::processIdaEvents();
		}
		break;


		// From final pass, we're done
		case eSTATE_FINISH:
		{
			// If there are more code segments to process, do next
			autoWait();
            if (chosen && !chosen->empty())
			{
				s_thisSeg = chosen->back();
                chosen->pop_back();
				s_segStart = s_thisSeg->startEA;
				s_segEnd   = s_thisSeg->endEA;
				s_state = eSTATE_START;
			}
			else
			{
				msg("\n===== Done =====\n");
				showEndStats();
                refresh_idaview_anyway();
				WaitBox::hide();
                WaitBox::processIdaEvents();

				// Optionally play completion sound
				if(s_audioAlertWhenDone)
				{
                    // Only if processing took at least a few seconds
                    if ((getTimeStamp() - s_startTime) > 2.2)
                    {

                        WaitBox::processIdaEvents();
                        OggPlay::playFromMemory((const PVOID)complete_ogg, complete_ogg_len);
                        OggPlay::endPlay();
                    }
				}

				s_state = eSTATE_EXIT;
			}
		}
		break;

		// Exit plugin run back to IDA control
		case eSTATE_EXIT:
		{
			// In case we aborted some place and list still exists..
            if (chosen)
            {
                SegSelect::free(chosen);
                chosen = NULL;
            }
			s_state = eSTATE_INIT;
		}
		break;
	};
}


// Print out end stats
static void showEndStats()
{
    char buffer[32];
	msg("Total time: %s\n", timeString(getTimeStamp() - s_startTime));
    msg("Alignments: %s\n", prettyNumberString(s_alignFixes, buffer));
    int functionsDelta = ((int) get_func_qty() - s_startFuncCount);
	if (functionsDelta != 0)
		msg(" Functions: %c%s\n", ((functionsDelta >= 0) ? '+' : '-'), prettyNumberString(labs(functionsDelta), buffer)); // Can be negative
	else
		msg(" Functions: 0\n");

	//msg("Code fixes: %u\n", s_uCodeFixes);
	//msg("Code fails: %u\n", s_uCodeFixFails);
	//msg("Align fails: %d\n", s_uAlignFails);
	//msg("  Unknowns: %u\n", s_uUnknowns);

	msg(" \n");
}

// Returns TRUE if flag byte is possibly a typical alignment byte
static bool idaapi isAlignByte(flags_t flags, void *ud)
{
	const flags_t ALIGN_VALUE1 = (FF_IVL | 0xCC); // 0xCC (single byte "int 3") byte type
	const flags_t ALIGN_VALUE2 = (FF_IVL | 0x90); // NOP byte type

	flags &= (FF_IVL | MS_VAL);
	if((flags == ALIGN_VALUE1) || (flags == ALIGN_VALUE2))
		return(TRUE);
	else
		return(FALSE);
}

// Return if flag is data type we want to convert to unknown bytes
static bool idaapi isData(flags_t flags, void *ud)
{
	return(!isAlign(flags) && isData(flags));
}


static inline BOOL isJmpNotCntl(UINT type) { return((type >= NN_jmp) && (type <= NN_jmpshort)); }   // Returns TRUE if is a non-conditional jump instruction type
static inline BOOL isCall(UINT type) { return((type >= NN_call) && (type <= NN_callni)); }          // Returns TRUE if is call instruction type

// Try adding a function at specified address
static BOOL tryFunction(ea_t codeStart, ea_t codeEnd, ea_t &current)
{
	BOOL result = FALSE;

	autoWait();
	#ifdef LOG_FILE
	Log(s_logFile, EAFORMAT " " EAFORMAT " Trying function.\n", codeStart, current);
	#endif
	//msg("  " EAFORMAT " " EAFORMAT " Trying function.\n", codeStart, codeEnd);

	/// *** Don't use "get_func()" it has a bug, use "get_fchunk()" instead ***

	// Could belong as a chunk to an existing function already or already a function here recovered already between steps.
	if(func_t *f = get_fchunk(codeStart))
	{
  		#ifdef LOG_FILE
        Log(s_logFile, "  " EAFORMAT " " EAFORMAT " " EAFORMAT " F: %08X already function.\n", f->endEA, f->startEA, codeStart, get_flags_novalue(codeStart));
		#endif
		//msg("  " EAFORMAT " " EAFORMAT " " EAFORMAT " F: %08X already a function.\n", f->endEA, f->startEA, codeStart, getFlags(codeStart));
		current = prev_head(f->endEA, codeStart); // Advance to end of the function -1 location (for a follow up "next_head()")
		result = TRUE;
	}
	else
	{
		// Try function here
		//flags_t flags = getFlags(codeEnd);
		//flags = flags;
		//if (add_func(codeStart, codeEnd /*BADADDR*/))

		if(add_func(codeStart, BADADDR))
		{
			// Wait till IDA is done possibly creating the function, then get it's info
			autoWait();
			if(func_t *f = get_fchunk(codeStart)) // get_func
			{
				#ifdef LOG_FILE
				Log(s_logFile, "  " EAFORMAT " function success.\n", codeStart);
				#endif
				#ifdef VBDEV
				msg("  " EAFORMAT " function success.\n", codeStart);
				#endif

				// Look at function tail instruction
				autoWait();
				BOOL isExpected = FALSE;
				ea_t tailEa = prev_head(f->endEA, codeStart);
				if(tailEa != BADADDR)
				{
					if(decode_insn(tailEa))
					{
						switch(cmd.itype)
						{
							// A return?
							case NN_retn: case NN_retf: case NN_iretw: case NN_iret: case NN_iretd:
							case NN_iretq: case NN_syscall:
							case NN_sysret:
							{
								isExpected = TRUE;
							}
							break;

							// A jump? (chain to another function, etc.)
							case NN_jmp: case NN_jmpfi:	case NN_jmpni: case NN_jmpshort:
							// Can be a conditional branch to another incongruent chunk
							case NN_ja:  case NN_jae: case NN_jb:  case NN_jbe:  case NN_jc:   case NN_je:   case NN_jg:
							case NN_jge: case NN_jl:  case NN_jle: case NN_jna:  case NN_jnae: case NN_jnb:  case NN_jnbe:
							case NN_jnc: case NN_jne: case NN_jng: case NN_jnge: case NN_jnl:  case NN_jnle: case NN_jno:
							case NN_jnp: case NN_jns: case NN_jnz: case NN_jo:   case NN_jp:  case NN_jpe:   case NN_jpo:
							case NN_js:  case NN_jz:
							{
								isExpected = TRUE;
							}
							break;

							// A single align byte that was mistakenly made a function?
							case NN_int3:
							case NN_nop:
							if(f->size() == 1)
							{
								// Try to make it an align
                                makeUnknown(tailEa, (tailEa + 1));
								if(!doAlign(tailEa, 1, 0))
								{
									// If it fails, make it an instruction at least
									//msg("  " EAFORMAT " ALIGN fail.\n", tailEA);
									create_insn(tailEa);
								}
                                autoWait();
								//msg("  " EAFORMAT " ALIGN\n", tailEA);
								isExpected = TRUE;
							}
							break;

							// Return-less exception or exit handler?
							case NN_call:
							{
								ea_t eaCRef = get_first_cref_from(tailEa);
								if(eaCRef != BADADDR)
								{
                                    qstring str;
                                    if (get_true_name(&str, eaCRef) > 0)
                                    {
                                        char name[MAXNAMELEN + 1];
                                        strncpy(name, str.c_str(), SIZESTR(name));
                                        _strlwr(name);

										static const char * const exitNames[] =
										{
											"exception",
											"handler",
											"exitprocess",
											"fatalappexit",
											"_abort",
											"_exit",
										};

										for(int i = 0; i < (sizeof(exitNames) / sizeof(const char *)); i++)
										{
											if(strstr(name, exitNames[i]))
											{
												//msg("  " EAFORMAT " Exception\n", CodeStartEA);
												isExpected = TRUE;
												break;
											}
										}
									}
								}
							}
							// Drop through to default for "call"

							// Allow if function has attribute "noreturn"
							default:
							{
								if(f->flags & FUNC_NORET)
								{
									//msg("  " EAFORMAT " NORETURN\n", tailEA);
									isExpected = TRUE;
								}
							}
							break;
						};
					}

					if(!isExpected)
					{
                        char name[MAXNAMELEN + 1];
                        qstring str;
                        if (get_true_name(&str, f->startEA) > 0)
                            strncpy(name, str.c_str(), SIZESTR(name));
                        else
                            memcpy(name, "unknown", sizeof("unknown"));
						msg(EAFORMAT " \"%s\" problem? <click me>\n", tailEa, name);
						//msg("  T: %d\n", cmd.itype);

						#ifdef LOG_FILE
						Log(s_logFile, EAFORMAT " \"%s\" problem? <click me>\n", tailEa, name);
						//Log(s_hLogFile, "  T: %d\n", cmd.itype);
						#endif
					}
				}

				// Update current look position to the end of this function
				current = tailEa; // Advance to end of the function -1 location (for a follow up "next_head()")
				result = TRUE;
			}
		}
	}

	return(result);
}


// Process the gap from the end of one function to the start of the next
// looking for missing functions in between.
static void processFuncGap(ea_t start, UINT size)
{
    s_currentAddress = start;
	ea_t end = (start + size);
	#ifdef LOG_FILE
	Log(s_logFile, "\nS: " EAFORMAT ", E: " EAFORMAT " ==== PFG START ====\n", start, end);
	#endif
	#ifdef VBDEV
	msg(EAFORMAT " " EAFORMAT " ==== Gap\n", start, end);
	#endif

	// Walk backwards at the end to trim alignments
	autoWait();
	ea_t ea = prev_head(end, start);
	if (ea == BADADDR)
		return;
	else
	{
		while (ea >= start)
		{
			flags_t flags = getFlags(ea);
			if (isAlignByte(flags, NULL) || isAlign(flags))
			{
				ea = prev_head(ea, start);
				if (ea == BADADDR)
					return;
			}
			else
			{
				end = next_head(ea, end);
				// Can fail in some odd circumstances, so reset it back to whole gap size
				if (end == BADADDR)
					end = (start + size);
				break;
			}
		};
	}

    // Traverse gap
	ea_t codeStart = BADADDR;
	ea = start;
    while(ea < end)
    {
		// Info flags for this address
        flags_t flags = getFlags(ea);
		#ifdef LOG_FILE
		Log(s_logFile, "  C: " EAFORMAT ", F: %08X, \"%s\".\n", ea, flags, getDisasmText(ea));
		#endif
		#ifdef VBDEV
		qstring disStr;
		getDisasmText(ea, disStr);
		msg(" C: " EAFORMAT ", F: %08X, \"%s\".\n", ea, flags, disStr.c_str());
		#endif

		if(ea < start)
		{
			#ifdef LOG_FILE
			Log(s_logFile, "**** Out of start range! " EAFORMAT " " EAFORMAT " " EAFORMAT " ****\n", ea, start, end);
			#endif
			return;
		}
        else
		if(ea > end)
		{
			#ifdef LOG_FILE
			Log(s_logFile, "**** Out of end range! " EAFORMAT " " EAFORMAT " " EAFORMAT " ****\n", ea, start, end);
			#endif
			return;
		}

		// Skip over "align" blocks.
		// #1 we will typically see more of these then anything else
		if(isAlignByte(flags, NULL) || isAlign(flags))
		{
			// Function between code start?
			if(codeStart != BADADDR)
			{
				#ifdef LOG_FILE
				Log(s_logFile, "  " EAFORMAT " Trying function #1\n", codeStart);
				#endif
				#ifdef VBDEV
				msg(">" EAFORMAT " Trying function #1\n", codeStart);
				#endif
				tryFunction(codeStart, end, ea);
			}

			codeStart = BADADDR;
		}
		else
		// #2 case, we'll typically see data
		if(isData(flags))
		{
			// Function between code start?
			if(codeStart != BADADDR)
			{
				#ifdef LOG_FILE
				Log(s_logFile, "  " EAFORMAT " Trying function #2\n", codeStart);
				#endif
				#ifdef VBDEV
				msg(">" EAFORMAT " Trying function #2\n", codeStart);
				#endif
				tryFunction(codeStart, end, ea);
			}

			codeStart = BADADDR;
		}
		else
		// Hit some code?
		if(isCode(flags))
		{
			// Yes, mark the start of a possible code block
			if(codeStart == BADADDR)
			{
				codeStart  = ea;

				#ifdef LOG_FILE
				Log(s_logFile, "  " EAFORMAT " Trying function #3, assumed func start\n", codeStart);
				#endif
				#ifdef VBDEV
				msg(">" EAFORMAT " Trying function #3, assumed func start\n", codeStart);
				#endif
				if(tryFunction(codeStart, end, ea))
					codeStart = BADADDR;
			}
		}
		else
		// Undefined?
		// Usually 0xCC align bytes
		if(isUnknown(flags))
		{
			#ifdef LOG_FILE
			Log(s_logFile, "  C: " EAFORMAT " , Unknown type.\n", ea);
			#endif
			#ifdef VBDEV
			msg("  C: " EAFORMAT ", Unknown type.\n", ea);
			#endif
			codeStart = BADADDR;
		}
		else
		{
			#ifdef LOG_FILE
			Log(s_logFile, "  " EAFORMAT " ** unknown data type! **\n", ea);
			#endif
			#ifdef VBDEV
			msg("  " EAFORMAT " ** unknown data type! **\n", ea);
			#endif
			codeStart = BADADDR;
		}

		// Next item
		autoWait();
		ea_t nextEa = BADADDR;
		if(ea != BADADDR)
		{
			nextEa = next_head(ea, end);
			if(nextEa != BADADDR)
				ea = nextEa;
		}

		if((nextEa == BADADDR) || (ea == BADADDR))
		{
			// If have code and at the end, try a function from the start
			if(codeStart != BADADDR)
			{
				#ifdef LOG_FILE
				Log(s_logFile, "  " EAFORMAT " Trying function #4\n", codeStart);
				#endif
				#ifdef VBDEV
				msg(">" EAFORMAT " Trying function #4\n", codeStart);
				#endif
				tryFunction(codeStart, end, ea);
				autoWait();
			}

			#ifdef LOG_FILE
			Log(s_logFile, " Gap end: " EAFORMAT ".\n", ea);
			#endif
			#ifdef VBDEV
			msg(" Gap end: " EAFORMAT ".\n", ea);
			#endif

            break;
		}

    }; // while(ea < start)
}

// ============================================================================

const char PLUGIN_NAME[] = "ExtraPass";

// Plug-in description block
extern "C" ALIGN(16) plugin_t PLUGIN =
{
	IDP_INTERFACE_VERSION,	// IDA version plug-in is written for
	PLUGIN_UNL,				// Plug-in flags
	plugin_init,			// Initialization function
	plugin_exit,	        // Clean-up function
	plugin_run,	            // Main plug-in body
	PLUGIN_NAME,	        // Comment - unused
	PLUGIN_NAME,	        // As above - unused
	PLUGIN_NAME,	        // Plug-in name shown in Edit->Plugins menu
	NULL                    // Hot key to run the plug-in
};
