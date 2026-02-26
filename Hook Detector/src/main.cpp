#include "imgui.h"
#include "imgui_impl_win32.h"
#include "imgui_impl_dx11.h"
#include <d3d11.h>
#include <tchar.h>
#include <vector>
#include <string>
#include <tlhelp32.h>
#include "winternl.h"
#include <format>
#include <thread>
#include "securitybaseapi.h"
#include <iostream>
#include <unordered_map>
#include <algorithm>
#pragma comment(lib, "d3d11.lib")




static ID3D11Device* g_pd3dDevice = nullptr;
static ID3D11DeviceContext* g_pd3dDeviceContext = nullptr;
static IDXGISwapChain* g_pSwapChain = nullptr;
static ID3D11RenderTargetView* g_mainRenderTargetView = nullptr;

bool createDeviceD3D(HWND hWnd);
void cleanupDeviceD3D();
void createRenderTarget();
void cleanupRenderTarget();
LRESULT WINAPI wndProc(HWND hWnd, UINT msg, WPARAM wParam, LPARAM lParam);
extern IMGUI_IMPL_API LRESULT ImGui_ImplWin32_WndProcHandler(HWND hWnd, UINT msg, WPARAM wParam, LPARAM lParam);




typedef __kernel_entry NTSTATUS NtQueryInformationProcess_t(
                HANDLE           ProcessHandle,
                int              ProcessInformationClass,
                PVOID            ProcessInformation,
                ULONG            ProcessInformationLength,
                PULONG           ReturnLength
);


NtQueryInformationProcess_t* fNtQueryInformationProcess = nullptr;


enum class Severity {
    Info,
    Warning,
    Detection,
    Critical
};

ImVec4 getSeverityColor(Severity s) {
    switch (s) {
    case Severity::Info:      return { 0.4f, 1.0f, 0.4f, 1.0f };   // green
    case Severity::Warning:   return { 1.0f, 0.8f, 0.2f, 1.0f };   // yellow
    case Severity::Detection: return { 1.0f, 0.4f, 0.4f, 1.0f };   // red
    case Severity::Critical:  return { 1.0f, 0.2f, 0.8f, 1.0f };   // magenta
    default:                  return { 1.0f, 1.0f, 1.0f, 1.0f };
    }
}

struct ScanResult {
    std::string description;
    Severity severity;
};


struct ProcessInfo {
    DWORD pid;
    wchar_t name[MAX_PATH];
};

struct ModuleInfo {
    std::string name;
    std::wstring fullPath;
    uintptr_t base;
    DWORD size;
    IMAGE_NT_HEADERS ntHeaders;
    BYTE* mappedFile;
    HANDLE hMapping;
};

static std::vector<ModuleInfo> g_modules;
static std::vector<ProcessInfo> g_processes;
static std::vector<ScanResult> g_results;
static std::unordered_map<std::string, ModuleInfo*> g_moduleMap;
static int g_selectedPid = 0;
static bool g_scanning = false;


void refreshProcessList() {
    g_processes.clear();
    HANDLE snap = CreateToolhelp32Snapshot(TH32CS_SNAPPROCESS, 0);
    if (snap == INVALID_HANDLE_VALUE) return;

    PROCESSENTRY32 pe = { sizeof(pe) };
    if (Process32First(snap, &pe)) {
        do {
            ProcessInfo info;
            info.pid = pe.th32ProcessID;
            wcscpy_s(info.name, pe.szExeFile);
            g_processes.push_back(info);
        } while (Process32Next(snap, &pe));
    }
    CloseHandle(snap);
}

bool isInTextSection(BYTE* fileBuffer, DWORD rva) {
    auto dos = (IMAGE_DOS_HEADER*)fileBuffer;
    auto nt = (IMAGE_NT_HEADERS*)(fileBuffer + dos->e_lfanew);
    auto section = IMAGE_FIRST_SECTION(nt);

    for (int i = 0; i < nt->FileHeader.NumberOfSections; i++) {
        if (strcmp((char*)section[i].Name, ".text") == 0) {
            return rva >= section[i].VirtualAddress &&
                rva < section[i].VirtualAddress + section[i].Misc.VirtualSize;
        }
    }
    return false;
}

void enableDebugPrivilege() {
    HANDLE token;
    OpenProcessToken(GetCurrentProcess(), TOKEN_ADJUST_PRIVILEGES, &token);

    TOKEN_PRIVILEGES tp;
    LookupPrivilegeValue(NULL, SE_DEBUG_NAME, &tp.Privileges[0].Luid);
    tp.PrivilegeCount = 1;
    tp.Privileges[0].Attributes = SE_PRIVILEGE_ENABLED;

    AdjustTokenPrivileges(token, FALSE, &tp, 0, NULL, NULL);
    CloseHandle(token);

}

uintptr_t resolveHookTarget(uint8_t* hookedBytes, uintptr_t address, HANDLE handle, int depth = 0) {
    if (depth >= 5) return 0;


    uintptr_t target = 0;

    // mov r64, imm64
    if ((hookedBytes[0] == 0x48 || hookedBytes[0] == 0x49) &&
        (hookedBytes[1] >= 0xB8 && hookedBytes[1] <= 0xBF)) {
       target = *reinterpret_cast<uintptr_t*>(hookedBytes + 2);
    }

    // jmp, xxxxx
    else if (hookedBytes[0] == 0xE9) {
        int32_t rel = *reinterpret_cast<int32_t*>(hookedBytes + 1);
        target = address + 5 + rel;

    }
    // jmp to pointer, so we need to deref it to get real address
    else if (hookedBytes[0] == 0xFF && hookedBytes[1] == 0x25) {
        int32_t rel = *reinterpret_cast<int32_t*>(hookedBytes + 2);
        uintptr_t ptrAddr = address + 6 + rel;
        ReadProcessMemory(handle, (LPCVOID)ptrAddr, &target, sizeof(target), nullptr);
    }

    if (target == 0) return 0;


    // follow jump chains recursively (e.g. E9 -> FF 25 -> final destination)
    BYTE nextBytes[16] = { 0 };
    if (ReadProcessMemory(handle, (LPCVOID)target, nextBytes, sizeof(nextBytes), nullptr)) {
        if (nextBytes[0] == 0xE9 || nextBytes[0] == 0xFF ||
            ((nextBytes[0] == 0x48 || nextBytes[0] == 0x49) && nextBytes[1] >= 0xB8 && nextBytes[1] <= 0xBF)) {
            return resolveHookTarget(nextBytes, target, handle, depth + 1);
        }
    }
    return target;
}

void cleanupModules() {
    for (auto& mod : g_modules) {
        if (mod.mappedFile) {
            UnmapViewOfFile(mod.mappedFile);
            mod.mappedFile = nullptr;
        }
        if (mod.hMapping) {
            CloseHandle(mod.hMapping);
            mod.hMapping = nullptr;
        }
    }
    g_modules.clear();
    g_moduleMap.clear();
}


void cacheModules(HANDLE handle) {
    cleanupModules();

    PROCESS_BASIC_INFORMATION pbi;
    ULONG returnLength;
    fNtQueryInformationProcess(handle, 0, &pbi, sizeof(pbi), &returnLength);

    PEB peb;
    ReadProcessMemory(handle, pbi.PebBaseAddress, &peb, sizeof(peb), nullptr);

    PEB_LDR_DATA ldr;
    ReadProcessMemory(handle, peb.Ldr, &ldr, sizeof(ldr), nullptr);

    LIST_ENTRY* head = (LIST_ENTRY*)((uintptr_t)peb.Ldr + offsetof(PEB_LDR_DATA, InMemoryOrderModuleList));
    LIST_ENTRY* current = ldr.InMemoryOrderModuleList.Flink;

    while (current != head) {
        LDR_DATA_TABLE_ENTRY entry;
        ReadProcessMemory(handle, (BYTE*)current - 0x10, &entry, sizeof(entry), nullptr);

        wchar_t dllName[MAX_PATH];
        ReadProcessMemory(handle, entry.FullDllName.Buffer, dllName, entry.FullDllName.Length, nullptr);
        dllName[entry.FullDllName.Length / sizeof(wchar_t)] = L'\0';

        auto base = (uintptr_t)entry.DllBase;

        IMAGE_DOS_HEADER dos;
        ReadProcessMemory(handle, (LPCVOID)base, &dos, sizeof(dos), nullptr);
        IMAGE_NT_HEADERS nt;
        ReadProcessMemory(handle, (LPCVOID)(base + dos.e_lfanew), &nt, sizeof(nt), nullptr);

        wchar_t* baseName = wcsrchr(dllName, L'\\');
        baseName = baseName ? baseName + 1 : dllName;

        char nameA[MAX_PATH];
        size_t conv;
        wcstombs_s(&conv, nameA, baseName, _TRUNCATE);

        BYTE* mappedFile = nullptr;
        HANDLE hMapping = nullptr;

        HANDLE hFile = CreateFileW(dllName, GENERIC_READ, FILE_SHARE_READ, nullptr, OPEN_EXISTING, 0, 0);
        if (hFile != INVALID_HANDLE_VALUE) {
            hMapping = CreateFileMappingW(hFile, nullptr, PAGE_READONLY | SEC_IMAGE, 0, 0, nullptr);
            if (hMapping) {
                mappedFile = (BYTE*)MapViewOfFile(hMapping, FILE_MAP_READ, 0, 0, 0);
            }
            CloseHandle(hFile);
        }


        g_modules.push_back({
            nameA,
            dllName,
            base,
            nt.OptionalHeader.SizeOfImage,
            nt,
            mappedFile,
            hMapping
            });

        current = entry.InMemoryOrderLinks.Flink;
    }

    for (auto& mod : g_modules) {
        std::string lower = mod.name;
        std::transform(lower.begin(), lower.end(), lower.begin(), ::tolower);
        g_moduleMap[lower] = &mod;
    }
}

std::string resolveAddressToModule(uintptr_t address) {

    for (auto& mod : g_modules) {
        if (address >= mod.base && address < mod.base + mod.size) {
            auto offset = address - mod.base;
            return std::format("{}-0x{:X}", mod.name, offset);
        }
    }
    return std::format("Unkown region-{:X}", address);
}





DWORD getExportRVA(BYTE* mappedFile, const char* funcName) {
    auto dos = (IMAGE_DOS_HEADER*)mappedFile;
    auto nt = (IMAGE_NT_HEADERS*)(mappedFile + dos->e_lfanew);

    if (nt->OptionalHeader.DataDirectory[IMAGE_DIRECTORY_ENTRY_EXPORT].VirtualAddress == 0)
        return 0;

    auto exportDir = (IMAGE_EXPORT_DIRECTORY*)(mappedFile +
        nt->OptionalHeader.DataDirectory[IMAGE_DIRECTORY_ENTRY_EXPORT].VirtualAddress);

    auto names = (DWORD*)(mappedFile + exportDir->AddressOfNames);
    auto functions = (DWORD*)(mappedFile + exportDir->AddressOfFunctions);
    auto ordinals = (WORD*)(mappedFile + exportDir->AddressOfNameOrdinals);

    for (DWORD i = 0; i < exportDir->NumberOfNames; i++) {
        auto name = (const char*)(mappedFile + names[i]);
        if (strcmp(name, funcName) == 0) {
            return functions[ordinals[i]];
        }
    }
    return 0;
}

void checkIATHooks(HANDLE handle, ModuleInfo& mod) {
    DWORD importRVA = mod.ntHeaders.OptionalHeader.DataDirectory[IMAGE_DIRECTORY_ENTRY_IMPORT].VirtualAddress;
    DWORD importSize = mod.ntHeaders.OptionalHeader.DataDirectory[IMAGE_DIRECTORY_ENTRY_IMPORT].Size;

    if (importRVA == 0 || importSize == 0) return;

    DWORD offset = importRVA;
    IMAGE_IMPORT_DESCRIPTOR importDesc{};

    while (true) {
        ReadProcessMemory(handle, (LPCVOID)(mod.base + offset), &importDesc, sizeof(importDesc), nullptr);
        if (importDesc.Name == NULL) break;

        if (importDesc.OriginalFirstThunk == 0) {
            offset += sizeof(IMAGE_IMPORT_DESCRIPTOR);
            continue;
        }

        char libName[MAX_PATH]{};
        ReadProcessMemory(handle, (LPCVOID)(mod.base + importDesc.Name), libName, sizeof(libName) - 1, nullptr);

        if (strncmp(libName, "api-ms-win-", 11) == 0 || strncmp(libName, "ext-ms-", 7) == 0) {
            offset += sizeof(IMAGE_IMPORT_DESCRIPTOR);
            continue;
        }


        std::string lib(libName);
        std::transform(lib.begin(), lib.end(), lib.begin(), ::tolower);
        auto it = g_moduleMap.find(lib);

        if (it == g_moduleMap.end()) {
            offset += sizeof(IMAGE_IMPORT_DESCRIPTOR);
            continue;
        }

       // std::cout << lib << std::endl;
        ModuleInfo* importedMod = it->second;

        DWORD iatOffset = importDesc.FirstThunk;
        DWORD intOffset = importDesc.OriginalFirstThunk;
        IMAGE_THUNK_DATA iat{}, intThunk{};

        while (true) {
            ReadProcessMemory(handle, (LPCVOID)(mod.base + intOffset), &intThunk, sizeof(intThunk), nullptr);
            ReadProcessMemory(handle, (LPCVOID)(mod.base + iatOffset), &iat, sizeof(iat), nullptr);

            if (intThunk.u1.AddressOfData == NULL) break;

            if (IMAGE_SNAP_BY_ORDINAL(intThunk.u1.Ordinal)) {
                intOffset += sizeof(IMAGE_THUNK_DATA);
                iatOffset += sizeof(IMAGE_THUNK_DATA);
                continue;
            }

            // IMAGE_IMPORT_BY_NAME = { WORD Hint, CHAR Name[1] }
            // Name[1] is a flexible array - actual string extends beyond the struct
            // We skip Hint (2 bytes) and read the name string directly
            char funcName[MAX_PATH]{};
            ReadProcessMemory(handle, (LPCVOID)(mod.base + intThunk.u1.AddressOfData + sizeof(WORD)), funcName, sizeof(funcName), nullptr); 

            DWORD expectedRVA = getExportRVA(importedMod->mappedFile, funcName);
            if (expectedRVA == 0) {
                intOffset += sizeof(IMAGE_THUNK_DATA);
                iatOffset += sizeof(IMAGE_THUNK_DATA);
                continue;
            }

            auto& exportEntry = importedMod->ntHeaders.OptionalHeader.DataDirectory[IMAGE_DIRECTORY_ENTRY_EXPORT];
            if (expectedRVA >= exportEntry.VirtualAddress &&
                expectedRVA < exportEntry.VirtualAddress + exportEntry.Size) {
                iatOffset += sizeof(IMAGE_THUNK_DATA);
                intOffset += sizeof(IMAGE_THUNK_DATA);
                continue;
            }


            uintptr_t expected = importedMod->base + expectedRVA;

            if (iat.u1.Function != expected) {
                auto target = resolveAddressToModule(iat.u1.Function);
                g_results.push_back({
                    std::format("[!] IAT Hook: {}!{}\n    Expected: 0x{:X} ({}+0x{:X})\n    Actual:   0x{:X} ({})",
                        mod.name, funcName,
                        expected, libName, expectedRVA,
                        iat.u1.Function, target),
                    Severity::Detection
                    });
            }

            iatOffset += sizeof(IMAGE_THUNK_DATA);
            intOffset += sizeof(IMAGE_THUNK_DATA);


        }
        offset += sizeof(IMAGE_IMPORT_DESCRIPTOR);
    }

}

void checkInlineHooks(HANDLE handle, ModuleInfo& mod) {
    auto exportDirRVA = mod.ntHeaders.OptionalHeader.DataDirectory[IMAGE_DIRECTORY_ENTRY_EXPORT].VirtualAddress;
    auto exportDirSize = mod.ntHeaders.OptionalHeader.DataDirectory[IMAGE_DIRECTORY_ENTRY_EXPORT].Size;

    if (exportDirRVA == 0 || exportDirSize == 0) return;
    if (!mod.mappedFile) return;

    IMAGE_EXPORT_DIRECTORY exportDir;
    ReadProcessMemory(handle, (LPCVOID)(mod.base + exportDirRVA), &exportDir, sizeof(exportDir), nullptr);

    if (exportDir.NumberOfNames == 0 || exportDir.NumberOfFunctions == 0) return;

    auto addressOfNames = new DWORD[exportDir.NumberOfNames];
    ReadProcessMemory(handle, (LPCVOID)(mod.base + exportDir.AddressOfNames),
        addressOfNames, exportDir.NumberOfNames * sizeof(DWORD), nullptr);

    auto addressOfFunctions = new DWORD[exportDir.NumberOfFunctions];
    ReadProcessMemory(handle, (LPCVOID)(mod.base + exportDir.AddressOfFunctions),
        addressOfFunctions, exportDir.NumberOfFunctions * sizeof(DWORD), nullptr);

    auto addressOfOrdinals = new WORD[exportDir.NumberOfNames];
    ReadProcessMemory(handle, (LPCVOID)(mod.base + exportDir.AddressOfNameOrdinals),
        addressOfOrdinals, exportDir.NumberOfNames * sizeof(WORD), nullptr);

    g_results.push_back({
        std::format("[+] Scanning: {} ({} exports)", mod.name, exportDir.NumberOfNames),
        Severity::Info
        });

    for (DWORD i = 0; i < exportDir.NumberOfNames; i++) {
        DWORD funcRVA = addressOfFunctions[addressOfOrdinals[i]];

        if (funcRVA == 0) continue;
        if (funcRVA >= exportDirRVA && funcRVA < exportDirRVA + exportDirSize) continue;
        if (!isInTextSection(mod.mappedFile, funcRVA)) continue;

        BYTE remoteBytes[16] = { 0 };
        ReadProcessMemory(handle, (LPCVOID)(mod.base + funcRVA), remoteBytes, sizeof(remoteBytes), nullptr);

        auto cleanBytes = mod.mappedFile + funcRVA;

        if (memcmp(remoteBytes, cleanBytes, 16) != 0) {
            char funcName[256]{};
            ReadProcessMemory(handle, (LPCVOID)(mod.base + addressOfNames[i]), funcName, sizeof(funcName) - 1, nullptr);

            char cleanHex[128]{}, remoteHex[128]{};
            int co = 0, ro = 0;
            for (int j = 0; j < 16; j++) {
                co += sprintf_s(cleanHex + co, sizeof(cleanHex) - co, "%02X ", cleanBytes[j]);
                ro += sprintf_s(remoteHex + ro, sizeof(remoteHex) - ro, "%02X ", remoteBytes[j]);
            }

            auto funcAddress = mod.base + funcRVA;
            auto targetAddress = resolveHookTarget(remoteBytes, funcAddress, handle);
            auto targetModule = resolveAddressToModule(targetAddress);

            g_results.push_back({
                std::format("[!] Inline Hook: {}!{}\n    Clean:  {}\n    Hooked: {}\n    Target: {}",
                    mod.name, funcName, cleanHex, remoteHex, targetModule),
                Severity::Detection
                });
        }
    }

    delete[] addressOfNames;
    delete[] addressOfFunctions;
    delete[] addressOfOrdinals;
}

void runScan(int pid) {
    g_results.clear();
    g_scanning = true;



    auto handle = OpenProcess(PROCESS_QUERY_INFORMATION | PROCESS_VM_READ, FALSE, pid);
    
    if (!handle) {
        auto error = GetLastError();
        g_results.push_back({
            std::format("[!] Failed to open handle to process: {}", error),
            Severity::Critical
            });
        g_scanning = false;
        return;
    }

    cacheModules(handle);

    g_results.push_back({
        std::format("[+] Found {} modules", g_modules.size()),
        Severity::Info
        });



    for (auto& mod : g_modules) {
        //std::cout << mod.name << std::endl;
        checkInlineHooks(handle, mod);
        checkIATHooks(handle, mod);
    }


    if (g_results.size() <= 1) {
        g_results.push_back({ "[+] No hooks detected.", Severity::Info });
    }

    cleanupModules();
    CloseHandle(handle);   
    g_scanning = false;
}

// ============================================================
// IMGUI RENDER
// ============================================================

void renderUI() {
    ImGui::SetNextWindowPos(ImVec2(0, 0));
    ImGui::SetNextWindowSize(ImGui::GetIO().DisplaySize);
    ImGui::Begin("Scanner", nullptr,
        ImGuiWindowFlags_NoResize |
        ImGuiWindowFlags_NoMove |
        ImGuiWindowFlags_NoCollapse |
        ImGuiWindowFlags_NoTitleBar);

    ImGui::TextColored(ImVec4(0.4f, 0.8f, 1.0f, 1.0f), "Hook Detector");
    ImGui::Separator();
    ImGui::Spacing();

    static int selectedIndex = -1;
    static char preview[512] = "Select process...";

    if (ImGui::Button("Refresh")) {
        refreshProcessList();
    }
    ImGui::SameLine();

    ImGui::SetNextItemWidth(300);
    if (ImGui::BeginCombo("##process", preview)) {
        for (int i = 0; i < g_processes.size(); i++) {
            char nameA[MAX_PATH];
            size_t converted;
            wcstombs_s(&converted, nameA, g_processes[i].name, _TRUNCATE);

            char label[512];
            sprintf_s(label, sizeof(label), "[%d] %s", g_processes[i].pid, nameA);

            if (ImGui::Selectable(label, selectedIndex == i)) {
                selectedIndex = i;
                g_selectedPid = g_processes[i].pid;
                sprintf_s(preview, sizeof(preview), "[%d] %s", g_processes[i].pid, nameA);
            }
        }
        ImGui::EndCombo();
    }

    ImGui::SameLine();
    if (ImGui::Button("Scan", ImVec2(100, 0))) {
        if (!g_scanning) {
            int pid = g_selectedPid;
            std::thread([pid]() {
                runScan(pid);
                }).detach();
        }
    }
    ImGui::SameLine();
    if (ImGui::Button("Clear", ImVec2(100, 0))) {
        g_results.clear();
    }

    ImGui::Spacing();
    ImGui::Separator();
    ImGui::Spacing();

    ImGui::Text("Results (%d)", (int)g_results.size());
    ImGui::BeginChild("Results", ImVec2(0, 0), true);

    for (auto& result : g_results) {
        ImGui::TextColored(getSeverityColor(result.severity), "%s", result.description.c_str());
    }

    ImGui::EndChild();
    ImGui::End();
}

// ============================================================
// WINMAIN + D3D BOILERPLATE
// ============================================================

int WINAPI WinMain(HINSTANCE hInstance, HINSTANCE, LPSTR, int) {


    fNtQueryInformationProcess = (NtQueryInformationProcess_t*)GetProcAddress(GetModuleHandleA("ntdll.dll"), "NtQueryInformationProcess");

    enableDebugPrivilege();

    AllocConsole();
    FILE* fs;
    freopen_s(&fs, "CONOUT$", "w", stdout);


    WNDCLASSEXW wc = {
        sizeof(wc), CS_CLASSDC, wndProc, 0L, 0L,
        GetModuleHandle(nullptr), nullptr, nullptr, nullptr, nullptr,
        L"ScannerClass", nullptr
    };
    RegisterClassExW(&wc);

    HWND hwnd = CreateWindowW(
        wc.lpszClassName, L"Scanner",
        WS_OVERLAPPEDWINDOW,
        100, 100, 800, 500,
        nullptr, nullptr, wc.hInstance, nullptr
    );

    if (!createDeviceD3D(hwnd)) {
        cleanupDeviceD3D();
        UnregisterClassW(wc.lpszClassName, wc.hInstance);
        return 1;
    }

    ShowWindow(hwnd, SW_SHOWDEFAULT);
    UpdateWindow(hwnd);

    IMGUI_CHECKVERSION();
    ImGui::CreateContext();
    ImGuiIO& io = ImGui::GetIO();
    io.ConfigFlags |= ImGuiConfigFlags_NavEnableKeyboard;

    ImGui::StyleColorsDark();
    ImGuiStyle& style = ImGui::GetStyle();
    style.WindowRounding = 0.0f;
    style.FrameRounding = 4.0f;
    style.GrabRounding = 4.0f;
    style.WindowBorderSize = 0.0f;
    style.FramePadding = ImVec2(8, 4);
    style.ItemSpacing = ImVec2(8, 6);

    style.Colors[ImGuiCol_Button] = ImVec4(0.20f, 0.40f, 0.65f, 1.00f);
    style.Colors[ImGuiCol_ButtonHovered] = ImVec4(0.28f, 0.50f, 0.75f, 1.00f);
    style.Colors[ImGuiCol_ButtonActive] = ImVec4(0.15f, 0.35f, 0.60f, 1.00f);
    style.Colors[ImGuiCol_FrameBg] = ImVec4(0.12f, 0.12f, 0.15f, 1.00f);
    style.Colors[ImGuiCol_WindowBg] = ImVec4(0.08f, 0.08f, 0.10f, 1.00f);
    style.Colors[ImGuiCol_ChildBg] = ImVec4(0.10f, 0.10f, 0.12f, 1.00f);

    ImGui_ImplWin32_Init(hwnd);
    ImGui_ImplDX11_Init(g_pd3dDevice, g_pd3dDeviceContext);

    MSG msg;
    ZeroMemory(&msg, sizeof(msg));

    refreshProcessList();

    while (msg.message != WM_QUIT) {
        if (PeekMessage(&msg, nullptr, 0U, 0U, PM_REMOVE)) {
            TranslateMessage(&msg);
            DispatchMessage(&msg);
            continue;
        }

        ImGui_ImplDX11_NewFrame();
        ImGui_ImplWin32_NewFrame();
        ImGui::NewFrame();

        renderUI();

        ImGui::Render();
        const float clear_color[4] = { 0.06f, 0.06f, 0.08f, 1.00f };
        g_pd3dDeviceContext->OMSetRenderTargets(1, &g_mainRenderTargetView, nullptr);
        g_pd3dDeviceContext->ClearRenderTargetView(g_mainRenderTargetView, clear_color);
        ImGui_ImplDX11_RenderDrawData(ImGui::GetDrawData());

        g_pSwapChain->Present(1, 0);
    }

    ImGui_ImplDX11_Shutdown();
    ImGui_ImplWin32_Shutdown();
    ImGui::DestroyContext();
    cleanupDeviceD3D();
    DestroyWindow(hwnd);
    UnregisterClassW(wc.lpszClassName, wc.hInstance);

    return 0;
}

// ============================================================
// D3D11 HELPERS
// ============================================================

bool createDeviceD3D(HWND hWnd) {
    DXGI_SWAP_CHAIN_DESC sd = {};
    sd.BufferCount = 2;
    sd.BufferDesc.Format = DXGI_FORMAT_R8G8B8A8_UNORM;
    sd.BufferUsage = DXGI_USAGE_RENDER_TARGET_OUTPUT;
    sd.OutputWindow = hWnd;
    sd.SampleDesc.Count = 1;
    sd.Windowed = TRUE;
    sd.SwapEffect = DXGI_SWAP_EFFECT_DISCARD;

    D3D_FEATURE_LEVEL featureLevel;
    if (D3D11CreateDeviceAndSwapChain(
        nullptr, D3D_DRIVER_TYPE_HARDWARE, nullptr, 0,
        nullptr, 0, D3D11_SDK_VERSION,
        &sd, &g_pSwapChain, &g_pd3dDevice, &featureLevel, &g_pd3dDeviceContext) != S_OK)
        return false;

    createRenderTarget();
    return true;
}

void cleanupDeviceD3D() {
    cleanupRenderTarget();
    if (g_pSwapChain) { g_pSwapChain->Release(); g_pSwapChain = nullptr; }
    if (g_pd3dDeviceContext) { g_pd3dDeviceContext->Release(); g_pd3dDeviceContext = nullptr; }
    if (g_pd3dDevice) { g_pd3dDevice->Release(); g_pd3dDevice = nullptr; }
}

void createRenderTarget() {
    ID3D11Texture2D* pBackBuffer;
    g_pSwapChain->GetBuffer(0, IID_PPV_ARGS(&pBackBuffer));
    g_pd3dDevice->CreateRenderTargetView(pBackBuffer, nullptr, &g_mainRenderTargetView);
    pBackBuffer->Release();
}

void cleanupRenderTarget() {
    if (g_mainRenderTargetView) { g_mainRenderTargetView->Release(); g_mainRenderTargetView = nullptr; }
}

LRESULT WINAPI wndProc(HWND hWnd, UINT msg, WPARAM wParam, LPARAM lParam) {
    if (ImGui_ImplWin32_WndProcHandler(hWnd, msg, wParam, lParam))
        return true;

    switch (msg) {
    case WM_SIZE:
        if (g_pd3dDevice && wParam != SIZE_MINIMIZED) {
            cleanupRenderTarget();
            g_pSwapChain->ResizeBuffers(0, (UINT)LOWORD(lParam), (UINT)HIWORD(lParam), DXGI_FORMAT_UNKNOWN, 0);
            createRenderTarget();
        }
        return 0;
    case WM_DESTROY:
        PostQuitMessage(0);
        return 0;
    }
    return DefWindowProcW(hWnd, msg, wParam, lParam);
}