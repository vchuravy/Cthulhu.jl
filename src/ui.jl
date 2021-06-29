using REPL.TerminalMenus
import REPL.TerminalMenus: request
using FoldingTrees

mutable struct CthulhuMenu <: TerminalMenus.AbstractMenu
    options::Vector{String}
    pagesize::Int
    pageoffset::Int
    selected::Int
    toggle::Union{Nothing, Symbol}
    sub_menu::Bool
end

function show_as_line(el, optimize::Bool)
    reduced_displaysize = displaysize(stdout)::Tuple{Int,Int} .- (0, 3)
    buf = ctx = IOBuffer()
    if (color = get(stdout, :color, nothing)) !== nothing
        ctx = IOContext(ctx, :color=>color)
    end
    show(IOContext(ctx, :limit=>true, :displaysize=>reduced_displaysize, :optimize=>optimize), el)
    String(take!(buf))
end


function CthulhuMenu(callsites, optimize::Bool; pagesize::Int=10, sub_menu = false)
    options = vcat(map(site->show_as_line(site, optimize), callsites), ["↩"])
    length(options) < 1 && error("CthulhuMenu must have at least one option")

    # if pagesize is -1, use automatic paging
    pagesize = pagesize == -1 ? length(options) : pagesize
    # pagesize shouldn't be bigger than options
    pagesize = min(length(options), pagesize)
    # after other checks, pagesize must be greater than 1
    pagesize < 1 && error("pagesize must be >= 1")

    pageoffset = 0
    selected = -1 # none

    CthulhuMenu(options, pagesize, pageoffset, selected, nothing, sub_menu)
end

TerminalMenus.options(m::CthulhuMenu) = m.options
TerminalMenus.cancel(m::CthulhuMenu) = m.selected = -1

function TerminalMenus.header(m::CthulhuMenu)
    m.sub_menu && return ""
    """
    Select a call to descend into or ↩ to ascend. [q]uit. [b]ookmark.
    Toggles: [o]ptimize, [w]arn, [v]erbose printing for warntype code, [d]ebuginfo, [i]nlining costs, [s]yntax highlight for Source/LLVM/Native.
    Show: [S]ource code, [A]ST, [L]LVM IR, [N]ative code
    Actions: [E]dit source code, [R]evise and redisplay
    Advanced: dump [P]arams cache.
    """
end

function TerminalMenus.keypress(m::CthulhuMenu, key::UInt32)
    m.sub_menu && return false
    if key == UInt32('w')
        m.toggle = :warn
        return true
    elseif key == UInt32('v')
        m.toggle = :verbose
        return true
    elseif key == UInt32('o')
        m.toggle = :optimize
        return true
    elseif key == UInt32('d')
        m.toggle = :debuginfo
        return true
    elseif key == UInt32('i')
        m.toggle = :inline_cost
        return true
    elseif key == UInt32('s')
        m.toggle = :highlighter
        return true
   elseif key == UInt32('S')
        m.toggle = :source
        return true
   elseif key == UInt32('A')
        m.toggle = :ast
        return true
    elseif key == UInt32('L')
        m.toggle = :llvm
        return true
    elseif key == UInt32('N')
        m.toggle = :native
        return true
    elseif key == UInt32('P')
        m.toggle = :dump_params
        return true
    elseif key == UInt32('b')
        m.toggle = :bookmark
        return true
    elseif key == UInt32('r') || key == UInt32('R')
        m.toggle = :revise
        return true
    elseif key == UInt32('e') || key == UInt32('E')
        m.toggle = :edit
        return true
    end
    return false
end

function TerminalMenus.pick(menu::CthulhuMenu, cursor::Int)
    menu.selected = cursor
    return true #break out of the menu
end

function TerminalMenus.writeLine(buf::IOBuffer, menu::CthulhuMenu, idx::Int, cursor::Bool)
    cursor_len = length(TerminalMenus.CONFIG[:cursor])
    # print a ">" on the selected entry
    cursor ? print(buf, TerminalMenus.CONFIG[:cursor]) : print(buf, repeat(" ", cursor_len))
    print(buf, " ") # Space between cursor and text

    line = replace(menu.options[idx], "\n" => "\\n")

    print(buf, line)
end

# This used to be the original method, the above is for compatibility with Base.REPL
function TerminalMenus.writeLine(buf::IOBuffer, menu::CthulhuMenu, idx::Int, cursor::Bool, term_width::Int)
    cursor_len = length(TerminalMenus.CONFIG[:cursor])
    # print a ">" on the selected entry
    cursor ? print(buf, TerminalMenus.CONFIG[:cursor]) : print(buf, repeat(" ", cursor_len))
    print(buf, " ") # Space between cursor and text

    line = replace(menu.options[idx], "\n" => "\\n")
    line = TerminalMenus.trimWidth(line, term_width, !cursor, cursor_len)

    print(buf, line)
end

function choose_method_instance(@nospecialize(sig); params=current_params())
    ci = callinfo(sig, Any, 1, params=params)
    ci isa MICallInfo && return get_mi(ci)
    ci isa Union{GeneratedCallInfo, FailedCallInfo} && return nothing
    if ci isa MultiCallInfo
        options = string.(ci.callinfos)
        menu = RadioMenu(options; charset=:unicode)
        chosen = request("Choose call to analyze:", menu)
        if chosen != -1
            return get_mi(ci.callinfos[chosen])
        end
    end
    error("unexpected callinfo ", ci)
end
