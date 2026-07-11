/**
 * App Logic - Paint Measurement Architect Tool
 * Handles 2D CAD canvas, snapping, dimension calculations, 3D visualization, and file operations.
 */

// --- Leaflet Map Globals ---
let leafletMap = null;
let leafletMap3D = null;
let mapLayersGroup = null;
let centerMarker = null;

// --- Global Application State ---
const state = {
    // Database
    vertices: [], // [{ id, x, y }] in meters
    walls: [],    // [{ id, v1Id, v2Id, thickness (m), height (m), type }]
    openings: [], // [{ id, wallId, type ('door'|'window'), offset (m), width (m), height (m), sillHeight (m) }]
    rooms: [],    // [{ id, name, vertices: [id], walls: [wallObj], area (m2) }]
    roomSettings: {}, // { [roomHash]: { name, paintWalls, paintCeiling } }
    isPrinting: false,
    globalExteriorHeight: 2.8,
    totalWallPaint: 0,
    totalCeilPaint: 0,
    totalTape: 0,
    totalWindowPaint: 0,
    totalExteriorPaint: 0,
    totalWallArea: 0,
    totalCeilArea: 0,
    totalWindowArea: 0,
    totalExteriorArea: 0,
    gpsLat: -37.8136,
    gpsLon: 144.9631,
    gpsRot: 0,
    show3DMap: false,
    mapStyle: 'street',
    
    // Viewport configuration
    viewMode: '2d', // '2d' or '3d'
    panX: 0,        // Panning translation (pixels)
    panY: 0,
    zoom: 40,       // Zoom scale (pixels per meter). Default: 1m = 40px
    gridSize: 1.0,  // Grid lines every 1m
    subGridSize: 0.1, // Subgrid every 10cm
    
    // Interaction states
    activeTool: 'select', // 'select' | 'wall' | 'door' | 'window'
    selectedWallPreset: 'exterior-std',
    customThickness: 120, // in mm
    
    // Selection state
    selectedElement: null, // { type: 'wall'|'opening', id }
    lockedVertexId: null,  // For wall resizing (locks 'start' or 'end' vertex)
    
    // Drawing wall state
    drawingStartVertexId: null,
    tempWallEnd: null,     // { x, y } in meters
    
    // Print and page guide settings
    pageSizeGuide: 'none', // 'none' | 'a4-portrait' | 'a4-landscape' | ...
    pagePos: { x: 0, y: 0 }, // Page center position in world space
    
    // Global Estimation constants
    globalWallHeight: 2.4, // meters
    paintCoverage: 10,     // m2 / Liter per coat
    wallCoats: 2,
    ceilingCoats: 2,
    applicationMethod: 'roller', // 'roller' (+10% waste) | 'spray' (+20% waste)
    shiftKey: false,
    activeAlignments: [],
    
    // 3D Scene variables
    three: {
        scene: null,
        camera: null,
        renderer: null,
        controls: null,
        animationFrameId: null,
        gridHelper: null,
        isOrbiting: false
    }
};

// Canvas references
let canvas2D, ctx2D;

// Initialize App
window.addEventListener('DOMContentLoaded', () => {
    initDOM();
    setupEventListeners();
    resetViewport();
    draw();
});

// --- DOM References & Initial Bindings ---
function initDOM() {
    canvas2D = document.getElementById('canvas-2d');
    ctx2D = canvas2D.getContext('2d');
    
    // Match canvas sizing to container
    resizeCanvas();
    window.addEventListener('resize', () => {
        resizeCanvas();
        draw();
    });
}

function resizeCanvas() {
    const rect = canvas2D.parentElement.getBoundingClientRect();
    canvas2D.width = rect.width;
    canvas2D.height = rect.height;
}

// --- Viewport Helpers ---
function resetViewport() {
    state.panX = canvas2D.width / 2;
    state.panY = canvas2D.height / 2;
    state.zoom = 40;
    state.pagePos = { x: 0, y: 0 };
}

// Screen to World coords
function screenToWorld(sx, sy) {
    return {
        x: (sx - state.panX) / state.zoom,
        y: (sy - state.panY) / state.zoom
    };
}

// World to Screen coords
function worldToScreen(wx, wy) {
    return {
        x: wx * state.zoom + state.panX,
        y: wy * state.zoom + state.panY
    };
}

// --- Snapping Engine ---
// Snaps screen coordinates to nearest vertex or wall segment.
// Returns snapped world coordinates, and the snapped elements details.
function getSnapPoint(sx, sy, excludeId = null) {
    const snapRadiusPx = 15;
    const clickWorld = screenToWorld(sx, sy);
    
    let bestSnap = { x: clickWorld.x, y: clickWorld.y, type: 'none', id: null };
    let minDistance = snapRadiusPx / state.zoom; // in meters
    
    // 1. Snap to Vertices
    for (const v of state.vertices) {
        if (v.id === excludeId) continue;
        const dist = Math.hypot(v.x - clickWorld.x, v.y - clickWorld.y);
        if (dist < minDistance) {
            minDistance = dist;
            bestSnap = { x: v.x, y: v.y, type: 'vertex', id: v.id };
        }
    }
    
    // 2. Snap to Wall Segments (only if we didn't snap to a vertex)
    if (bestSnap.type === 'none') {
        for (const w of state.walls) {
            const v1 = findVertex(w.v1Id);
            const v2 = findVertex(w.v2Id);
            if (!v1 || !v2) continue;
            
            const proj = projectPointOnSegment(clickWorld, v1, v2);
            if (proj.onSegment) {
                const dist = Math.hypot(proj.x - clickWorld.x, proj.y - clickWorld.y);
                if (dist < minDistance) {
                    minDistance = dist;
                    bestSnap = { x: proj.x, y: proj.y, type: 'wall', id: w.id };
                }
            }
        }
    }
    
    // 3. Smart alignment snapping (Align with other vertices horizontally/vertically)
    state.activeAlignments = [];
    if (bestSnap.type !== 'vertex') {
        const screenSnap = worldToScreen(bestSnap.x, bestSnap.y);
        let snappedH = false;
        let snappedV = false;
        
        for (const v of state.vertices) {
            if (v.id === excludeId) continue;
            if (state.activeTool === 'wall' && v.id === state.drawingStartVertexId) continue;
            
            const screenV = worldToScreen(v.x, v.y);
            
            // Align horizontally (same Y)
            if (!snappedH && Math.abs(screenV.y - screenSnap.y) < 12) {
                bestSnap.y = v.y;
                snappedH = true;
                state.activeAlignments.push({
                    type: 'horizontal',
                    y: v.y,
                    x1: bestSnap.x,
                    x2: v.x
                });
            }
            
            // Align vertically (same X)
            if (!snappedV && Math.abs(screenV.x - screenSnap.x) < 12) {
                bestSnap.x = v.x;
                snappedV = true;
                state.activeAlignments.push({
                    type: 'vertical',
                    x: v.x,
                    y1: bestSnap.y,
                    y2: v.y
                });
            }
        }
    }
    
    return bestSnap;
}

// Project point P onto segment AB
function projectPointOnSegment(p, a, b) {
    const abX = b.x - a.x;
    const abY = b.y - a.y;
    const apX = p.x - a.x;
    const apY = p.y - a.y;
    
    const ab2 = abX * abX + abY * abY;
    if (ab2 === 0) return { x: a.x, y: a.y, onSegment: false };
    
    let t = (apX * abX + apY * abY) / ab2;
    const onSegment = t >= 0 && t <= 1;
    t = Math.max(0, Math.min(1, t));
    
    return {
        x: a.x + t * abX,
        y: a.y + t * abY,
        onSegment: onSegment
    };
}

// --- Data Helpers ---
function findVertex(id) {
    return state.vertices.find(v => v.id === id);
}

function findWall(id) {
    return state.walls.find(w => w.id === id);
}

function findOpening(id) {
    return state.openings.find(op => op.id === id);
}

function getWallThickness(type) {
    switch (type) {
        case 'exterior-brick': return 0.250;
        case 'exterior-weatherboard': return 0.112;
        case 'exterior-std': return 0.150;
        case 'interior-std': return 0.120;
        case 'custom': return state.customThickness / 1000;
        default: return 0.120;
    }
}

// --- Event Handlers & Core Canvas Control ---
let isPanning = false;
let panStartX, panStartY;
let activeDragVertexId = null;
let activeDragOpeningId = null;

function setupEventListeners() {
    // Tool buttons
    const toolButtons = ['tool-select', 'tool-wall', 'tool-door', 'tool-window'];
    toolButtons.forEach(id => {
        document.getElementById(id).addEventListener('click', (e) => {
            toolButtons.forEach(b => document.getElementById(b).classList.remove('active'));
            const btn = e.currentTarget;
            btn.classList.add('active');
            state.activeTool = id.replace('tool-', '');
            
            // Cancel drawing if changing tool
            if (state.activeTool !== 'wall') {
                state.drawingStartVertexId = null;
                state.tempWallEnd = null;
            }
            deselectElement();
            draw();
        });
    });

    // Preset listener
    document.getElementById('wall-preset').addEventListener('change', (e) => {
        const preset = e.target.value;
        state.selectedWallPreset = preset;
        const customGroup = document.getElementById('custom-thickness-group');
        if (preset === 'custom') {
            customGroup.classList.remove('hidden');
        } else {
            customGroup.classList.add('hidden');
        }
    });

    document.getElementById('wall-custom-thickness').addEventListener('input', (e) => {
        state.customThickness = parseFloat(e.target.value) || 120;
    });

    // Global Configs
    document.getElementById('cfg-wall-height').addEventListener('input', (e) => {
        state.globalWallHeight = parseFloat(e.target.value) || 2.4;
        recalculateAll();
        draw();
    });
    document.getElementById('cfg-ext-height').addEventListener('input', (e) => {
        state.globalExteriorHeight = parseFloat(e.target.value) || 2.8;
        recalculateAll();
        draw();
    });
    document.getElementById('cfg-coverage').addEventListener('input', (e) => {
        state.paintCoverage = parseFloat(e.target.value) || 10;
        recalculateAll();
        draw();
    });
    document.getElementById('cfg-wall-coats').addEventListener('input', (e) => {
        state.wallCoats = parseInt(e.target.value) || 2;
        recalculateAll();
        draw();
    });
    document.getElementById('cfg-ceil-coats').addEventListener('input', (e) => {
        state.ceilingCoats = parseInt(e.target.value) || 2;
        recalculateAll();
        draw();
    });
    document.getElementById('cfg-method').addEventListener('change', (e) => {
        state.applicationMethod = e.target.value;
        recalculateAll();
        draw();
    });

    // Zoom Buttons
    document.getElementById('btn-zoom-in').addEventListener('click', () => { zoomAtCenter(1.2); });
    document.getElementById('btn-zoom-out').addEventListener('click', () => { zoomAtCenter(0.85); });
    document.getElementById('btn-zoom-fit').addEventListener('click', zoomToFit);

    // View Toggle
    document.getElementById('btn-view-2d').addEventListener('click', () => toggleViewMode('2d'));
    document.getElementById('btn-view-3d').addEventListener('click', () => toggleViewMode('3d'));
    document.getElementById('btn-view-map').addEventListener('click', () => toggleViewMode('map'));
    document.getElementById('btn-3d-map-toggle').addEventListener('click', toggle3DMapBackground);
    document.getElementById('btn-3d-orbit').addEventListener('click', toggle3DOrbit);

    // Print & Clear
    document.getElementById('btn-print').addEventListener('click', () => {
        deselectElement();
        state.isPrinting = true;
        draw();
        setTimeout(() => {
            window.print();
            state.isPrinting = false;
            draw();
        }, 100);
    });
    
    document.getElementById('btn-clear').addEventListener('click', () => {
        if (confirm('Clear the entire project plan?')) {
            state.vertices = [];
            state.walls = [];
            state.openings = [];
            state.rooms = [];
            deselectElement();
            recalculateAll();
            draw();
        }
    });

    // Page Guide
    document.getElementById('page-size').addEventListener('change', (e) => {
        state.pageSizeGuide = e.target.value;
        draw();
    });

    // File Operations
    document.getElementById('btn-save').addEventListener('click', saveProject);
    document.getElementById('btn-export-kml').addEventListener('click', exportKML);
    document.getElementById('file-upload').addEventListener('change', loadProject);
    
    // Location Events
    document.getElementById('cfg-gps-lat').addEventListener('change', (e) => {
        state.gpsLat = parseFloat(e.target.value) || -37.8136;
        if (leafletMap && centerMarker) {
            centerMarker.setLatLng([state.gpsLat, state.gpsLon]);
            leafletMap.setView([state.gpsLat, state.gpsLon]);
            drawMapPlan();
        }
    });
    document.getElementById('cfg-gps-lon').addEventListener('change', (e) => {
        state.gpsLon = parseFloat(e.target.value) || 144.9631;
        if (leafletMap && centerMarker) {
            centerMarker.setLatLng([state.gpsLat, state.gpsLon]);
            leafletMap.setView([state.gpsLat, state.gpsLon]);
            drawMapPlan();
        }
    });
    document.getElementById('btn-get-gps').addEventListener('click', () => {
        if (navigator.geolocation) {
            navigator.geolocation.getCurrentPosition(
                (position) => {
                    state.gpsLat = position.coords.latitude;
                    state.gpsLon = position.coords.longitude;
                    document.getElementById('cfg-gps-lat').value = state.gpsLat.toFixed(6);
                    document.getElementById('cfg-gps-lon').value = state.gpsLon.toFixed(6);
                    if (leafletMap && centerMarker) {
                        centerMarker.setLatLng([state.gpsLat, state.gpsLon]);
                        leafletMap.setView([state.gpsLat, state.gpsLon]);
                        drawMapPlan();
                    }
                },
                (error) => {
                    alert('Could not retrieve current location: ' + error.message);
                }
            );
        } else {
            alert('Geolocation is not supported by your browser.');
        }
    });
    document.getElementById('cfg-gps-rot').addEventListener('input', (e) => {
        state.gpsRot = parseFloat(e.target.value) || 0;
        const valSpan = document.getElementById('cfg-gps-rot-val');
        if (valSpan) valSpan.innerText = `${state.gpsRot}°`;
        if (leafletMap) {
            drawMapPlan();
        }
    });
    document.getElementById('cfg-map-style').addEventListener('change', (e) => {
        state.mapStyle = e.target.value;
        updateMapLayers();
    });

    // Inspector Events
    document.getElementById('insp-wall-length').addEventListener('change', handleWallLengthChange);
    document.getElementById('insp-wall-length').addEventListener('keydown', (e) => {
        if (e.key === 'Enter') {
            e.target.blur();
        }
    });
    document.getElementById('btn-lock-start').addEventListener('click', () => setLockVertex('start'));
    document.getElementById('btn-lock-end').addEventListener('click', () => setLockVertex('end'));
    document.getElementById('insp-wall-thickness').addEventListener('change', handleWallThicknessChange);
    document.getElementById('insp-wall-preset').addEventListener('change', handleWallPresetChange);
    document.getElementById('btn-delete-wall').addEventListener('click', deleteSelectedElement);

    // Opening Inspector Events
    document.getElementById('insp-op-width').addEventListener('change', handleOpeningEdit);
    document.getElementById('insp-op-height').addEventListener('change', handleOpeningEdit);
    document.getElementById('insp-op-sill').addEventListener('change', handleOpeningEdit);
    document.getElementById('insp-op-offset').addEventListener('change', handleOpeningEdit);
    document.getElementById('insp-door-hinge').addEventListener('change', handleOpeningEdit);
    document.getElementById('insp-door-swing').addEventListener('change', handleOpeningEdit);
    document.getElementById('btn-delete-op').addEventListener('click', deleteSelectedElement);

    // Room Inspector Events
    document.getElementById('insp-room-name').addEventListener('input', (e) => {
        if (!state.selectedElement || state.selectedElement.type !== 'room') return;
        const room = state.rooms.find(r => r.id === state.selectedElement.id);
        if (!room) return;
        
        const hash = getRoomHash(room.vertices);
        if (!state.roomSettings[hash]) {
            state.roomSettings[hash] = { name: room.name, paintWalls: true, paintCeiling: true };
        }
        state.roomSettings[hash].name = e.target.value;
        recalculateAll();
        draw();
    });
    document.getElementById('insp-room-paint-walls').addEventListener('change', (e) => {
        if (!state.selectedElement || state.selectedElement.type !== 'room') return;
        const room = state.rooms.find(r => r.id === state.selectedElement.id);
        if (!room) return;
        
        const hash = getRoomHash(room.vertices);
        if (!state.roomSettings[hash]) {
            state.roomSettings[hash] = { name: room.name, paintWalls: true, paintCeiling: true };
        }
        state.roomSettings[hash].paintWalls = e.target.checked;
        recalculateAll();
        draw();
    });
    document.getElementById('insp-room-paint-ceiling').addEventListener('change', (e) => {
        if (!state.selectedElement || state.selectedElement.type !== 'room') return;
        const room = state.rooms.find(r => r.id === state.selectedElement.id);
        if (!room) return;
        
        const hash = getRoomHash(room.vertices);
        if (!state.roomSettings[hash]) {
            state.roomSettings[hash] = { name: room.name, paintWalls: true, paintCeiling: true };
        }
        state.roomSettings[hash].paintCeiling = e.target.checked;
        recalculateAll();
        draw();
    });
    
    // Double click to rename room
    canvas2D.addEventListener('dblclick', handleDoubleClick);

    // --- Mouse interaction on Canvas ---
    canvas2D.addEventListener('mousedown', handleMouseDown);
    canvas2D.addEventListener('mousemove', handleMouseMove);
    canvas2D.addEventListener('mouseup', handleMouseUp);
    canvas2D.addEventListener('wheel', handleWheel);
    canvas2D.addEventListener('mouseleave', () => {
        state.hoverX = null;
        state.hoverY = null;
        if (state.viewMode === '2d') draw();
    });

    // Key events
    window.addEventListener('keydown', (e) => {
        if (e.key === 'Shift') {
            state.shiftKey = true;
            draw();
        }
        if (e.key === 'Escape') {
            if (state.activeTool === 'wall') {
                state.drawingStartVertexId = null;
                state.tempWallEnd = null;
                draw();
            }
        }
        if (e.key === 'Delete' || e.key === 'Backspace') {
            // Ignore key events if focused on input boxes
            if (document.activeElement.tagName === 'INPUT' || document.activeElement.tagName === 'SELECT') return;
            deleteSelectedElement();
        }
    });

    window.addEventListener('keyup', (e) => {
        if (e.key === 'Shift') {
            state.shiftKey = false;
            draw();
        }
    });
}

function zoomAtCenter(factor) {
    const oldZoom = state.zoom;
    state.zoom = Math.max(5, Math.min(200, state.zoom * factor));
    
    // Zoom around the center of the canvas screen
    const cx = canvas2D.width / 2;
    const cy = canvas2D.height / 2;
    
    const worldCenter = {
        x: (cx - state.panX) / oldZoom,
        y: (cy - state.panY) / oldZoom
    };
    
    state.panX = cx - worldCenter.x * state.zoom;
    state.panY = cy - worldCenter.y * state.zoom;
    
    document.getElementById('zoom-level').innerText = `Scale: 1:${Math.round(50 * (40 / state.zoom))}`;
    draw();
}

function zoomToFit() {
    if (state.vertices.length === 0) {
        resetViewport();
        draw();
        return;
    }
    
    // Compute bounds
    let minX = Infinity, maxX = -Infinity;
    let minY = Infinity, maxY = -Infinity;
    state.vertices.forEach(v => {
        minX = Math.min(minX, v.x);
        maxX = Math.max(maxX, v.x);
        minY = Math.min(minY, v.y);
        maxY = Math.max(maxY, v.y);
    });
    
    const boundsW = maxX - minX;
    const boundsH = maxY - minY;
    
    // Add margin
    const margin = 2.0; // meters
    const totalW = boundsW + margin * 2;
    const totalH = boundsH + margin * 2;
    
    const scaleX = canvas2D.width / totalW;
    const scaleY = canvas2D.height / totalH;
    state.zoom = Math.max(10, Math.min(150, Math.min(scaleX, scaleY)));
    
    // Center it
    const centerX = minX + boundsW / 2;
    const centerY = minY + boundsH / 2;
    state.panX = canvas2D.width / 2 - centerX * state.zoom;
    state.panY = canvas2D.height / 2 - centerY * state.zoom;
    
    document.getElementById('zoom-level').innerText = `Scale: 1:${Math.round(50 * (40 / state.zoom))}`;
    draw();
}

function handleWheel(e) {
    e.preventDefault();
    
    const mx = e.clientX - canvas2D.getBoundingClientRect().left;
    const my = e.clientY - canvas2D.getBoundingClientRect().top;
    
    // Get mouse world coordinates before zoom changes
    const worldMouse = screenToWorld(mx, my);
    
    const factor = e.deltaY < 0 ? 1.15 : 0.85;
    state.zoom = Math.max(5, Math.min(200, state.zoom * factor));
    
    // Adjust pan coordinates so the mouse remains focused on the same world location
    state.panX = mx - worldMouse.x * state.zoom;
    state.panY = my - worldMouse.y * state.zoom;
    
    document.getElementById('zoom-level').innerText = `Scale: 1:${Math.round(50 * (40 / state.zoom))}`;
    draw();
}

function handleMouseDown(e) {
    const mx = e.clientX - canvas2D.getBoundingClientRect().left;
    const my = e.clientY - canvas2D.getBoundingClientRect().top;
    
    // Middle mouse button or Space bar/Ctrl to Pan
    if (e.button === 1 || e.button === 2 || (e.button === 0 && e.shiftKey && state.activeTool === 'select')) {
        isPanning = true;
        panStartX = mx - state.panX;
        panStartY = my - state.panY;
        canvas2D.style.cursor = 'grabbing';
        return;
    }
    
    if (e.button !== 0) return; // Left click only for actions
    
    const snap = getSnapPoint(mx, my);
    
    // 1. SELECT TOOL
    if (state.activeTool === 'select') {
        // Check if clicked a vertex handle
        if (snap.type === 'vertex') {
            activeDragVertexId = snap.id;
            selectWallByVertex(snap.id);
            return;
        }
        
        // Check if clicked a door/window opening
        const opId = getClickedOpening(mx, my);
        if (opId) {
            activeDragOpeningId = opId;
            selectElement('opening', opId);
            draw();
            return;
        }
        
        // Check if clicked a wall segment
        const wallId = getClickedWall(mx, my);
        if (wallId) {
            selectElement('wall', wallId);
            draw();
            return;
        }
        
        // Check if clicked a room
        const roomId = getClickedRoom(mx, my);
        if (roomId) {
            selectElement('room', roomId);
            draw();
            return;
        }
        
        // Clicked empty space
        deselectElement();
        draw();
    }
    
    // 2. WALL TOOL (Point-to-Point)
    else if (state.activeTool === 'wall') {
        let snapX = snap.x;
        let snapY = snap.y;
        
        if (state.drawingStartVertexId) {
            const startV = findVertex(state.drawingStartVertexId);
            const snapped = getAngleSnappedPoint({x: startV.x, y: startV.y}, {x: snapX, y: snapY}, state.shiftKey);
            snapX = snapped.x;
            snapY = snapped.y;
        }
        
        // Create/Find start vertex
        let vStartId = state.drawingStartVertexId;
        
        if (vStartId === null) {
            // First point of new wall
            if (snap.type === 'vertex') {
                vStartId = snap.id;
            } else if (snap.type === 'wall') {
                // Split wall on snap point
                vStartId = splitWallAtPoint(snap.id, snap.x, snap.y);
            } else {
                vStartId = createVertex(snapX, snapY);
            }
            state.drawingStartVertexId = vStartId;
        } else {
            // Second point of wall - close and create wall segment
            let vEndId;
            if (snap.type === 'vertex') {
                vEndId = snap.id;
            } else if (snap.type === 'wall') {
                vEndId = splitWallAtPoint(snap.id, snap.x, snap.y);
            } else {
                vEndId = createVertex(snapX, snapY);
            }
            
            if (vStartId !== vEndId) {
                createWall(vStartId, vEndId);
                recalculateAll();
            }
            
            // Continue drawing wall chain from end vertex
            state.drawingStartVertexId = vEndId;
        }
        draw();
    }
    
    // 3. DOOR / WINDOW PLACEMENT TOOL
    else if (state.activeTool === 'door' || state.activeTool === 'window') {
        const wallId = getClickedWall(mx, my);
        if (wallId) {
            const wObj = findWall(wallId);
            const v1 = findVertex(wObj.v1Id);
            const v2 = findVertex(wObj.v2Id);
            const clickW = screenToWorld(mx, my);
            const proj = projectPointOnSegment(clickW, v1, v2);
            
            const wallLength = Math.hypot(v2.x - v1.x, v2.y - v1.y);
            const offset = Math.hypot(proj.x - v1.x, proj.y - v1.y);
            
            // Create opening
            const opType = state.activeTool;
            const w = opType === 'door' ? 0.9 : 1.2;
            const h = opType === 'door' ? 2.1 : 1.2;
            const sill = opType === 'door' ? 0.0 : 0.9;
            
            // Clamp offset so opening fits on wall
            const clampedOffset = Math.max(0, Math.min(wallLength - w, offset - w/2));
            
            const opId = 'op_' + Date.now();
            state.openings.push({
                id: opId,
                wallId: wallId,
                type: opType,
                offset: clampedOffset,
                width: w,
                height: h,
                sillHeight: sill
            });
            
            selectElement('opening', opId);
            recalculateAll();
        }
        draw();
    }
}

function handleMouseMove(e) {
    const rect = canvas2D.getBoundingClientRect();
    const mx = e.clientX - rect.left;
    const my = e.clientY - rect.top;
    
    // Save hover position for snap indicator drawing
    state.hoverX = mx;
    state.hoverY = my;
    
    if (isPanning) {
        state.panX = mx - panStartX;
        state.panY = my - panStartY;
        draw();
        return;
    }
    
    // Dragging Vertex
    if (activeDragVertexId) {
        const worldCoords = screenToWorld(mx, my);
        const vertex = findVertex(activeDragVertexId);
        
        // Snapping coordinates during drag
        const snap = getSnapPoint(mx, my, activeDragVertexId);
        let targetX = worldCoords.x;
        let targetY = worldCoords.y;
        
        if (snap.type === 'vertex' && snap.id !== activeDragVertexId) {
            targetX = snap.x;
            targetY = snap.y;
        } else {
            // Apply angle snapping relative to reference vertex
            let refVertexId = null;
            if (state.selectedElement && state.selectedElement.type === 'wall') {
                const wall = findWall(state.selectedElement.id);
                if (wall.v1Id === activeDragVertexId) refVertexId = wall.v2Id;
                else if (wall.v2Id === activeDragVertexId) refVertexId = wall.v1Id;
            }
            if (!refVertexId) {
                // Find first connected wall
                const connWall = state.walls.find(w => w.v1Id === activeDragVertexId || w.v2Id === activeDragVertexId);
                if (connWall) {
                    refVertexId = connWall.v1Id === activeDragVertexId ? connWall.v2Id : connWall.v1Id;
                }
            }
            
            if (refVertexId) {
                const refV = findVertex(refVertexId);
                const snapped = getAngleSnappedPoint({x: refV.x, y: refV.y}, {x: targetX, y: targetY}, state.shiftKey);
                targetX = snapped.x;
                targetY = snapped.y;
            }
        }
        
        vertex.x = targetX;
        vertex.y = targetY;
        
        recalculateAll();
        draw();
        return;
    }
    
    // Dragging Door/Window along its wall
    if (activeDragOpeningId) {
        const op = findOpening(activeDragOpeningId);
        const wall = findWall(op.wallId);
        const v1 = findVertex(wall.v1Id);
        const v2 = findVertex(wall.v2Id);
        const worldCoords = screenToWorld(mx, my);
        
        const proj = projectPointOnSegment(worldCoords, v1, v2);
        const wallLength = Math.hypot(v2.x - v1.x, v2.y - v1.y);
        const offset = Math.hypot(proj.x - v1.x, proj.y - v1.y);
        
        // Clamp door offset so it stays within wall bounds
        op.offset = Math.max(0, Math.min(wallLength - op.width, offset - op.width / 2));
        
        // Update input field in Inspector
        const field = document.getElementById('insp-op-offset');
        if (field) field.value = op.offset.toFixed(2);
        
        recalculateAll();
        draw();
        return;
    }
    
    // Active Drawing line update
    if (state.activeTool === 'wall' && state.drawingStartVertexId) {
        const snap = getSnapPoint(mx, my, state.drawingStartVertexId);
        let endX = snap.x;
        let endY = snap.y;
        
        const startV = findVertex(state.drawingStartVertexId);
        const snapped = getAngleSnappedPoint({x: startV.x, y: startV.y}, {x: endX, y: endY}, state.shiftKey);
        endX = snapped.x;
        endY = snapped.y;
        
        state.tempWallEnd = { x: endX, y: endY };
        draw();
    }
    
    // Cursor hover style feedback
    if (state.activeTool === 'select') {
        const snap = getSnapPoint(mx, my);
        const hoverOp = getClickedOpening(mx, my);
        const hoverWall = getClickedWall(mx, my);
        
        if (snap.type === 'vertex' || hoverOp || hoverWall) {
            canvas2D.style.cursor = 'pointer';
        } else {
            canvas2D.style.cursor = 'default';
        }
    }
    
    if (state.viewMode === '2d') {
        draw();
    }
}

function handleMouseUp(e) {
    if (isPanning) {
        isPanning = false;
        canvas2D.style.cursor = 'default';
        return;
    }
    
    activeDragVertexId = null;
    activeDragOpeningId = null;
}

// Draw wall snapping angle lock helper
// Snaps to 90 degrees by default, and 2.5 degrees if shiftKey is active
function getAngleSnappedPoint(start, current, shiftKey) {
    const dx = current.x - start.x;
    const dy = current.y - start.y;
    const distance = Math.hypot(dx, dy);
    if (distance === 0) return current;
    
    let angle = Math.atan2(dy, dx);
    
    let step = (2.5 * Math.PI) / 180; // 2.5 degrees in radians
    if (shiftKey) {
        step = Math.PI / 2; // 90 degrees in radians
    }
    
    angle = Math.round(angle / step) * step;
    
    return {
        x: start.x + distance * Math.cos(angle),
        y: start.y + distance * Math.sin(angle)
    };
}

// --- Entity Creation ---
function createVertex(x, y) {
    const id = 'v_' + Date.now() + Math.random().toString(36).substr(2, 5);
    state.vertices.push({ id, x, y });
    return id;
}

function createWall(v1Id, v2Id) {
    // Avoid double walls on exact same vertices
    const duplicate = state.walls.find(w => 
        (w.v1Id === v1Id && w.v2Id === v2Id) || 
        (w.v1Id === v2Id && w.v2Id === v1Id)
    );
    if (duplicate) return duplicate.id;
    
    const id = 'w_' + Date.now() + Math.random().toString(36).substr(2, 5);
    const thickness = getWallThickness(state.selectedWallPreset);
    
    state.walls.push({
        id,
        v1Id,
        v2Id,
        thickness: thickness,
        height: state.globalWallHeight,
        type: state.selectedWallPreset
    });
    return id;
}

// Split wall into two sections by placing a new vertex at (x,y) on the wall segment
function splitWallAtPoint(wallId, x, y) {
    const wObj = findWall(wallId);
    if (!wObj) return null;
    
    const newVertexId = createVertex(x, y);
    const oldV2 = wObj.v2Id;
    
    // Split the wall. wObj links v1Id -> newVertexId
    wObj.v2Id = newVertexId;
    
    // Create new wall linking newVertexId -> oldV2
    const nextWallId = createWall(newVertexId, oldV2);
    
    // Move any openings on the original wall to the correct wall section
    const wLengthTotal = Math.hypot(findVertex(newVertexId).x - findVertex(wObj.v1Id).x, findVertex(newVertexId).y - findVertex(wObj.v1Id).y);
    
    const wallOpenings = state.openings.filter(op => op.wallId === wallId);
    wallOpenings.forEach(op => {
        if (op.offset > wLengthTotal) {
            // Moves to the split off wall section
            op.wallId = nextWallId;
            op.offset -= wLengthTotal;
        }
    });
    
    return newVertexId;
}

// --- Select Wall by Vertex ---
function selectWallByVertex(vertexId) {
    const connectedWalls = state.walls.filter(w => w.v1Id === vertexId || w.v2Id === vertexId);
    if (connectedWalls.length > 0) {
        selectElement('wall', connectedWalls[0].id);
    }
}

// --- Selection Panel Updates ---
function selectElement(type, id) {
    state.selectedElement = { type, id };
    
    document.getElementById('inspector-empty').classList.add('hidden');
    
    if (type === 'wall') {
        document.getElementById('inspector-wall').classList.remove('hidden');
        document.getElementById('inspector-opening').classList.add('hidden');
        
        const wObj = findWall(id);
        const v1 = findVertex(wObj.v1Id);
        const v2 = findVertex(wObj.v2Id);
        const len = Math.hypot(v2.x - v1.x, v2.y - v1.y);
        
        document.getElementById('insp-wall-length').value = len.toFixed(2);
        document.getElementById('insp-wall-thickness').value = Math.round(wObj.thickness * 1000);
        const presetSelect = document.getElementById('insp-wall-preset');
        if (presetSelect) {
            presetSelect.value = wObj.type || 'custom';
        }
        
        // Reset locked vertex default if not set
        if (!state.lockedVertexId || (state.lockedVertexId !== wObj.v1Id && state.lockedVertexId !== wObj.v2Id)) {
            state.lockedVertexId = wObj.v1Id;
        }
        
        // Update UI lock button states, colors and labels
        if (state.lockedVertexId === wObj.v1Id) {
            document.getElementById('btn-lock-start').classList.add('active');
            document.getElementById('btn-lock-end').classList.remove('active');
            document.getElementById('btn-lock-start').innerHTML = '<span class="material-icons" style="color: #10b981;">lock</span> Lock A (Green)';
            document.getElementById('btn-lock-end').innerHTML = '<span class="material-icons" style="color: #9ca3af;">lock_open</span> Lock B (Gray)';
        } else {
            document.getElementById('btn-lock-start').classList.remove('active');
            document.getElementById('btn-lock-end').classList.add('active');
            document.getElementById('btn-lock-start').innerHTML = '<span class="material-icons" style="color: #9ca3af;">lock_open</span> Lock A (Gray)';
            document.getElementById('btn-lock-end').innerHTML = '<span class="material-icons" style="color: #10b981;">lock</span> Lock B (Green)';
        }

        // Auto focus and select dimension text
        setTimeout(() => {
            const lenInput = document.getElementById('insp-wall-length');
            if (lenInput) {
                lenInput.focus();
                lenInput.select();
            }
        }, 50);
    } 
    
    else if (type === 'opening') {
        document.getElementById('inspector-wall').classList.add('hidden');
        document.getElementById('inspector-opening').classList.remove('hidden');
        document.getElementById('inspector-room').classList.add('hidden');
        
        const op = findOpening(id);
        document.getElementById('insp-op-title').innerText = op.type === 'door' ? 'Door Segment' : 'Window Segment';
        document.getElementById('insp-op-width').value = op.width.toFixed(2);
        document.getElementById('insp-op-height').value = op.height.toFixed(2);
        document.getElementById('insp-op-sill').value = op.sillHeight.toFixed(2);
        document.getElementById('insp-op-offset').value = op.offset.toFixed(2);
        
        // Show/hide door hinge & swing settings
        const doorSwingGroup = document.getElementById('door-swing-group');
        if (op.type === 'door') {
            if (doorSwingGroup) doorSwingGroup.classList.remove('hidden');
            const hingeSelect = document.getElementById('insp-door-hinge');
            const swingSelect = document.getElementById('insp-door-swing');
            if (hingeSelect) hingeSelect.value = op.hingeSide || 'left';
            if (swingSelect) swingSelect.value = op.swingDir || 'out';
        } else {
            if (doorSwingGroup) doorSwingGroup.classList.add('hidden');
        }
        
        // Set maximum offset limit on inspector
        const wall = findWall(op.wallId);
        const v1 = findVertex(wall.v1Id);
        const v2 = findVertex(wall.v2Id);
        const len = Math.hypot(v2.x - v1.x, v2.y - v1.y);
        document.getElementById('insp-op-offset').max = (len - op.width).toFixed(2);
    }
    
    else if (type === 'room') {
        document.getElementById('inspector-wall').classList.add('hidden');
        document.getElementById('inspector-opening').classList.add('hidden');
        document.getElementById('inspector-room').classList.remove('hidden');
        
        const room = state.rooms.find(r => r.id === id);
        if (room) {
            const hash = getRoomHash(room.vertices);
            const settings = state.roomSettings[hash] || { name: room.name, paintWalls: true, paintCeiling: true };
            
            document.getElementById('insp-room-name').value = settings.name || room.name;
            document.getElementById('insp-room-paint-walls').checked = settings.paintWalls !== false;
            document.getElementById('insp-room-paint-ceiling').checked = settings.paintCeiling !== false;
        }
    }
}

function deselectElement() {
    state.selectedElement = null;
    document.getElementById('inspector-empty').classList.remove('hidden');
    document.getElementById('inspector-wall').classList.add('hidden');
    document.getElementById('inspector-opening').classList.add('hidden');
    document.getElementById('inspector-room').classList.add('hidden');
}

function setLockVertex(mode) {
    if (state.selectedElement && state.selectedElement.type === 'wall') {
        const wObj = findWall(state.selectedElement.id);
        if (mode === 'start') {
            state.lockedVertexId = wObj.v1Id;
            document.getElementById('btn-lock-start').classList.add('active');
            document.getElementById('btn-lock-end').classList.remove('active');
            document.getElementById('btn-lock-start').innerHTML = '<span class="material-icons" style="color: #10b981;">lock</span> Lock A (Green)';
            document.getElementById('btn-lock-end').innerHTML = '<span class="material-icons" style="color: #9ca3af;">lock_open</span> Lock B (Gray)';
        } else {
            state.lockedVertexId = wObj.v2Id;
            document.getElementById('btn-lock-start').classList.remove('active');
            document.getElementById('btn-lock-end').classList.add('active');
            document.getElementById('btn-lock-start').innerHTML = '<span class="material-icons" style="color: #9ca3af;">lock_open</span> Lock A (Gray)';
            document.getElementById('btn-lock-end').innerHTML = '<span class="material-icons" style="color: #10b981;">lock</span> Lock B (Green)';
        }
        draw();
    }
}

// Change wall length inside editor panel
function handleWallLengthChange(e) {
    if (!state.selectedElement || state.selectedElement.type !== 'wall') return;
    const newLen = parseFloat(e.target.value);
    if (!newLen || newLen <= 0.05) return;
    
    const wObj = findWall(state.selectedElement.id);
    const vStart = findVertex(wObj.v1Id);
    const vEnd = findVertex(wObj.v2Id);
    
    const angle = Math.atan2(vEnd.y - vStart.y, vEnd.x - vStart.x);
    
    // Resize by shifting the unlocked vertex position
    if (state.lockedVertexId === wObj.v1Id) {
        // v1 (Start) is Locked: shift v2 (End) position
        vEnd.x = vStart.x + newLen * Math.cos(angle);
        vEnd.y = vStart.y + newLen * Math.sin(angle);
    } else {
        // v2 (End) is Locked: shift v1 (Start) position
        vStart.x = vEnd.x - newLen * Math.cos(angle);
        vStart.y = vEnd.y - newLen * Math.sin(angle);
    }
    
    recalculateAll();
    draw();
}

function handleWallThicknessChange(e) {
    if (!state.selectedElement || state.selectedElement.type !== 'wall') return;
    const thickMm = parseFloat(e.target.value);
    if (!thickMm || thickMm <= 0) return;
    
    const wObj = findWall(state.selectedElement.id);
    wObj.thickness = thickMm / 1000;
    wObj.type = 'custom';
    
    const presetSelect = document.getElementById('insp-wall-preset');
    if (presetSelect) presetSelect.value = 'custom';
    
    recalculateAll();
    draw();
}

function handleWallPresetChange(e) {
    if (!state.selectedElement || state.selectedElement.type !== 'wall') return;
    const preset = e.target.value;
    const wObj = findWall(state.selectedElement.id);
    if (!wObj) return;
    
    wObj.type = preset;
    if (preset !== 'custom') {
        wObj.thickness = getWallThickness(preset);
        document.getElementById('insp-wall-thickness').value = Math.round(wObj.thickness * 1000);
    }
    recalculateAll();
    draw();
}

function handleOpeningEdit() {
    if (!state.selectedElement || state.selectedElement.type !== 'opening') return;
    const op = findOpening(state.selectedElement.id);
    if (!op) return;
    
    const wallObj = findWall(op.wallId);
    const v1 = findVertex(wallObj.v1Id);
    const v2 = findVertex(wallObj.v2Id);
    const wallLength = Math.hypot(v2.x - v1.x, v2.y - v1.y);
    
    const width = parseFloat(document.getElementById('insp-op-width').value) || 0.9;
    const height = parseFloat(document.getElementById('insp-op-height').value) || 2.1;
    const sill = parseFloat(document.getElementById('insp-op-sill').value) || 0.0;
    const offset = parseFloat(document.getElementById('insp-op-offset').value) || 0.0;
    
    op.width = Math.min(wallLength, Math.max(0.1, width));
    op.height = Math.max(0.1, height);
    op.sillHeight = Math.max(0.0, sill);
    op.offset = Math.max(0, Math.min(wallLength - op.width, offset));
    
    // Hinge Side and Swing Direction for doors
    if (op.type === 'door') {
        const hingeSelect = document.getElementById('insp-door-hinge');
        const swingSelect = document.getElementById('insp-door-swing');
        if (hingeSelect) op.hingeSide = hingeSelect.value;
        if (swingSelect) op.swingDir = swingSelect.value;
    }
    
    // Refresh inspector values
    document.getElementById('insp-op-width').value = op.width.toFixed(2);
    document.getElementById('insp-op-height').value = op.height.toFixed(2);
    document.getElementById('insp-op-sill').value = op.sillHeight.toFixed(2);
    document.getElementById('insp-op-offset').value = op.offset.toFixed(2);
    document.getElementById('insp-op-offset').max = (wallLength - op.width).toFixed(2);
    
    recalculateAll();
    draw();
}

function deleteSelectedElement() {
    if (!state.selectedElement) return;
    const { type, id } = state.selectedElement;
    
    if (type === 'wall') {
        // Delete openings attached to wall first
        state.openings = state.openings.filter(op => op.wallId !== id);
        // Delete wall
        state.walls = state.walls.filter(w => w.id !== id);
        // Clean orphan vertices
        cleanOrphanVertices();
    } else if (type === 'opening') {
        state.openings = state.openings.filter(op => op.id !== id);
    }
    
    deselectElement();
    recalculateAll();
    draw();
}

function cleanOrphanVertices() {
    state.vertices = state.vertices.filter(v => {
        return state.walls.some(w => w.v1Id === v.id || w.v2Id === v.id);
    });
}

// Click collision selectors
function getClickedWall(mx, my) {
    const clickWorld = screenToWorld(mx, my);
    const clickRadius = 12 / state.zoom;
    
    for (const w of state.walls) {
        const v1 = findVertex(w.v1Id);
        const v2 = findVertex(w.v2Id);
        if (!v1 || !v2) continue;
        
        // Midpoint check (for measurement text click hit detection)
        const midX = (v1.x + v2.x) / 2;
        const midY = (v1.y + v2.y) / 2;
        const distToMid = Math.hypot(midX - clickWorld.x, midY - clickWorld.y);
        const midClickRadius = 25 / state.zoom; // 25px in meters around midpoint
        if (distToMid < midClickRadius) {
            return w.id;
        }
        
        const proj = projectPointOnSegment(clickWorld, v1, v2);
        if (proj.onSegment) {
            const dist = Math.hypot(proj.x - clickWorld.x, proj.y - clickWorld.y);
            if (dist < clickRadius + w.thickness/2) {
                return w.id;
            }
        }
    }
    return null;
}

function getClickedOpening(mx, my) {
    const clickWorld = screenToWorld(mx, my);
    const clickRadius = 12 / state.zoom;
    
    for (const op of state.openings) {
        const wall = findWall(op.wallId);
        const v1 = findVertex(wall.v1Id);
        const v2 = findVertex(wall.v2Id);
        
        const angle = Math.atan2(v2.y - v1.y, v2.x - v1.x);
        
        // Find center of opening in world space
        const opCenterX = v1.x + (op.offset + op.width / 2) * Math.cos(angle);
        const opCenterY = v1.y + (op.offset + op.width / 2) * Math.sin(angle);
        
        const dist = Math.hypot(clickWorld.x - opCenterX, clickWorld.y - opCenterY);
        if (dist < clickRadius + op.width / 2) {
            return op.id;
        }
    }
    return null;
}

function getClickedRoom(mx, my) {
    const clickWorld = screenToWorld(mx, my);
    for (const room of state.rooms) {
        const polyPoints = room.vertices.map(vId => findVertex(vId)).filter(v => v);
        if (polyPoints.length >= 3 && isPointInPolygon(clickWorld, polyPoints)) {
            return room.id;
        }
    }
    return null;
}

function isPointInPolygon(p, polygon) {
    let isInside = false;
    const n = polygon.length;
    for (let i = 0, j = n - 1; i < n; j = i++) {
        const vi = polygon[i];
        const vj = polygon[j];
        if (((vi.y > p.y) !== (vj.y > p.y)) &&
            (p.x < (vj.x - vi.x) * (p.y - vi.y) / (vj.y - vi.y) + vi.x)) {
            isInside = !isInside;
        }
    }
    return isInside;
}

function getRoomHash(vertexIds) {
    return [...vertexIds].sort().join(',');
}

function handleDoubleClick(e) {
    const mx = e.clientX - canvas2D.getBoundingClientRect().left;
    const my = e.clientY - canvas2D.getBoundingClientRect().top;
    
    if (state.activeTool === 'select') {
        const roomId = getClickedRoom(mx, my);
        if (roomId) {
            const room = state.rooms.find(r => r.id === roomId);
            if (room) {
                const hash = getRoomHash(room.vertices);
                const currentSettings = state.roomSettings[hash] || { name: room.name, paintWalls: true, paintCeiling: true };
                const newName = prompt('Enter new room name:', currentSettings.name || room.name);
                if (newName !== null) {
                    const trimmed = newName.trim();
                    if (trimmed) {
                        currentSettings.name = trimmed;
                        state.roomSettings[hash] = currentSettings;
                        recalculateAll();
                        if (state.selectedElement && state.selectedElement.type === 'room' && state.selectedElement.id === roomId) {
                            selectElement('room', roomId);
                        }
                        draw();
                    }
                }
            }
        }
    }
}

// --- Geometric Room Solver & Calculations Engine ---
function recalculateAll() {
    // 1. Solve Rooms
    solveRooms();
    // 2. Compute Quantities
    computePaintDashboard();
}

function solveRooms() {
    state.rooms = [];
    if (state.vertices.length < 3 || state.walls.length < 3) return;
    
    // Build adjacency list for vertices
    const adj = {};
    state.vertices.forEach(v => { adj[v.id] = []; });
    
    state.walls.forEach(w => {
        if (w.v1Id === w.v2Id) return;
        
        // Check both vertices exist
        if (!adj[w.v1Id] || !adj[w.v2Id]) return;
        
        adj[w.v1Id].push({ to: w.v2Id, wall: w });
        adj[w.v2Id].push({ to: w.v1Id, wall: w });
    });
    
    // Sort neighbors counter-clockwise
    state.vertices.forEach(v => {
        adj[v.id].sort((a, b) => {
            const va = findVertex(a.to);
            const vb = findVertex(b.to);
            const angleA = Math.atan2(va.y - v.y, va.x - v.x);
            const angleB = Math.atan2(vb.y - v.y, vb.x - v.x);
            return angleA - angleB;
        });
    });
    
    const visited = new Set();
    const faces = [];
    
    // Planar Graph Face Tracing
    state.vertices.forEach(v => {
        adj[v.id].forEach(edge => {
            const edgeKey = `${v.id}->${edge.to}`;
            if (visited.has(edgeKey)) return;
            
            const path = [];
            const wallList = [];
            let curr = v.id;
            let next = edge.to;
            
            while (true) {
                const key = `${curr}->${next}`;
                if (visited.has(key)) break;
                visited.add(key);
                
                path.push(curr);
                
                // Add wall reference
                const neighbors = adj[curr];
                const edgeObj = neighbors.find(n => n.to === next);
                if (edgeObj) wallList.push(edgeObj.wall);
                
                // Predecessor trace
                const nextNeighbors = adj[next];
                const idx = nextNeighbors.findIndex(n => n.to === curr);
                if (idx === -1) break;
                
                const nextIdx = (idx - 1 + nextNeighbors.length) % nextNeighbors.length;
                const nextNext = nextNeighbors[nextIdx].to;
                
                curr = next;
                next = nextNext;
                
                if (curr === v.id && next === edge.to) {
                    break;
                }
            }
            
            if (path.length >= 3) {
                // Compute Shoelace Area
                let area = 0;
                for (let i = 0; i < path.length; i++) {
                    const p1 = findVertex(path[i]);
                    const p2 = findVertex(path[(i + 1) % path.length]);
                    area += (p1.x * p2.y - p2.x * p1.y);
                }
                area = 0.5 * area;
                
                faces.push({
                    vertices: path,
                    walls: wallList,
                    area: area
                });
            }
        });
    });
    
    if (faces.length <= 1) return;
    
    // Sort faces by absolute area. The largest absolute area face is the exterior bounds.
    faces.sort((a, b) => Math.abs(a.area) - Math.abs(b.area));
    
    // The last face is the outer exterior polygon, pop it.
    faces.pop();
    
    // Map remaining faces to rooms
    faces.forEach((f, index) => {
        const hash = getRoomHash(f.vertices);
        const savedName = (state.roomSettings[hash] && state.roomSettings[hash].name) || `Room ${index + 1}`;
        
        // Enforce positive area value for display calculations
        state.rooms.push({
            id: 'room_' + index,
            name: savedName,
            vertices: f.vertices,
            walls: f.walls,
            area: Math.abs(f.area)
        });
    });
}

function computePaintDashboard() {
    const tableBody = document.getElementById('rooms-breakdown-body');
    tableBody.innerHTML = '';
    
    // Wastage Multiplier
    const wasteMultiplier = state.applicationMethod === 'spray' ? 1.20 : 1.10;
    
    // 1. Exterior Walls paint calculation (minus windows)
    let totalExtWallLength = 0;
    let totalExtWindowArea = 0;
    const extWindowsSummary = [];
    
    state.walls.forEach(w => {
        if (w.type && w.type.startsWith('exterior')) {
            const v1 = findVertex(w.v1Id);
            const v2 = findVertex(w.v2Id);
            if (!v1 || !v2) return;
            
            const len = Math.hypot(v2.x - v1.x, v2.y - v1.y);
            totalExtWallLength += len;
            
            // Find windows on this exterior wall
            const wallWindows = state.openings.filter(op => op.wallId === w.id && op.type === 'window');
            wallWindows.forEach(op => {
                totalExtWindowArea += op.width * op.height;
                extWindowsSummary.push(`Win(${op.width}x${op.height})`);
            });
        }
    });
    
    const grossExtArea = totalExtWallLength * state.globalExteriorHeight;
    const netExtArea = Math.max(0, grossExtArea - totalExtWindowArea);
    const extPaint = totalExtWallLength > 0 ? (netExtArea / state.paintCoverage) * state.wallCoats * wasteMultiplier : 0;
    
    // 2. Window Frame Trim paint calculation
    let totalWindowTrimArea = 0;
    let windowCount = 0;
    const windowDetails = [];
    
    // Sum from rooms
    state.rooms.forEach(room => {
        const hash = getRoomHash(room.vertices);
        const settings = state.roomSettings[hash] || { name: room.name, paintWalls: true, paintCeiling: true };
        if (settings.paintWalls !== false) {
            room.walls.forEach(w => {
                const wallWindows = state.openings.filter(op => op.wallId === w.id && op.type === 'window');
                wallWindows.forEach(op => {
                    totalWindowTrimArea += 2 * (op.width + op.height) * 0.08;
                    windowCount++;
                    windowDetails.push(`${settings.name || room.name}: Win(${op.width}x${op.height})`);
                });
            });
        }
    });
    
    // Sum from exterior walls
    state.walls.forEach(w => {
        if (w.type && w.type.startsWith('exterior')) {
            const wallWindows = state.openings.filter(op => op.wallId === w.id && op.type === 'window');
            wallWindows.forEach(op => {
                totalWindowTrimArea += 2 * (op.width + op.height) * 0.08;
                windowCount++;
                windowDetails.push(`Exterior: Win(${op.width}x${op.height})`);
            });
        }
    });
    
    const windowPaint = totalWindowTrimArea > 0 ? (totalWindowTrimArea / state.paintCoverage) * state.wallCoats * wasteMultiplier : 0;
    
    if (state.rooms.length === 0) {
        tableBody.innerHTML = `<tr><td colspan="7" class="empty-table-msg">Draw closed walls to detect rooms and compute paint requirements.</td></tr>`;
        
        // Remove empty message row if adding details
        if (totalExtWallLength > 0 || totalWindowTrimArea > 0) {
            const emptyMsg = tableBody.querySelector('.empty-table-msg');
            if (emptyMsg) emptyMsg.parentNode.remove();
        }
        
        // Append Exterior row to breakdown table even if no rooms exist
        if (totalExtWallLength > 0) {
            const tr = document.createElement('tr');
            tr.style.background = 'rgba(6, 182, 212, 0.05)';
            tr.innerHTML = `
                <td><strong>Exterior Walls</strong></td>
                <td>No Ceiling</td>
                <td>${netExtArea.toFixed(2)} m²</td>
                <td>0.0 L</td>
                <td>${extPaint.toFixed(1)} L</td>
                <td>0.0 m</td>
                <td>${extWindowsSummary.join(', ') || 'None'}</td>
            `;
            tableBody.appendChild(tr);
        }
        
        // Append Window row even if no rooms exist
        if (totalWindowTrimArea > 0) {
            const tr = document.createElement('tr');
            tr.style.background = 'rgba(234, 88, 12, 0.04)';
            tr.innerHTML = `
                <td><strong>Window Frame Trim</strong></td>
                <td>No Ceiling</td>
                <td>${totalWindowTrimArea.toFixed(2)} m²</td>
                <td>0.0 L</td>
                <td>${windowPaint.toFixed(1)} L</td>
                <td>0.0 m</td>
                <td>${windowDetails.join(', ') || 'None'}</td>
            `;
            tableBody.appendChild(tr);
        }
        
        // Render Summary Cards Block
        const totalsBlock = document.getElementById('dashboard-totals-block');
        if (totalsBlock) {
            let totalExtTape = 0;
            state.walls.forEach(w => {
                if (w.type && w.type.startsWith('exterior')) {
                    const wallWindows = state.openings.filter(op => op.wallId === w.id && op.type === 'window');
                    wallWindows.forEach(op => {
                        totalExtTape += 2 * (op.width + op.height);
                    });
                }
            });

            totalsBlock.innerHTML = `
                <div class="total-card">
                    <span class="lbl">Wall Paint</span>
                    <span class="val">0.0<span class="unit-s"> L</span></span>
                    <span class="sub">0.0 m² (${state.wallCoats} coats)</span>
                </div>
                <div class="total-card">
                    <span class="lbl">Ceiling Paint</span>
                    <span class="val">0.0<span class="unit-s"> L</span></span>
                    <span class="sub">0.0 m² (${state.ceilingCoats} coats)</span>
                </div>
                <div class="total-card">
                    <span class="lbl">Masking Tape Inside</span>
                    <span class="val">0.0<span class="unit-s"> m</span></span>
                    <span class="sub">(Rooms & Openings)</span>
                </div>
                <div class="total-card">
                    <span class="lbl">Masking Tape Outside</span>
                    <span class="val">${totalExtTape.toFixed(1)}<span class="unit-s"> m</span></span>
                    <span class="sub">(Around each window)</span>
                </div>
                <div class="total-card">
                    <span class="lbl">Windows Paint</span>
                    <span class="val">${windowPaint.toFixed(1)}<span class="unit-s"> L</span></span>
                    <span class="sub">${totalWindowTrimArea.toFixed(1)} m² (${state.wallCoats} coats)</span>
                </div>
                <div class="total-card">
                    <span class="lbl">Exterior Paint</span>
                    <span class="val">${extPaint.toFixed(1)}<span class="unit-s"> L</span></span>
                    <span class="sub">${netExtArea.toFixed(1)} m² (${state.wallCoats} coats)</span>
                </div>
            `;
        }
        
        state.totalWallPaint = 0;
        state.totalCeilPaint = 0;
        state.totalTape = 0;
        state.totalWindowPaint = windowPaint;
        state.totalExteriorPaint = extPaint;
        state.totalWallArea = 0;
        state.totalCeilArea = 0;
        state.totalWindowArea = totalWindowTrimArea;
        state.totalExteriorArea = netExtArea;
        
        updateGrandTotals(0, 0, 0, 0, 0, 0, extPaint, netExtArea, windowPaint, totalWindowTrimArea);
        return;
    }
    
    let totalCeilAreaSum = 0;
    let totalWallAreaSum = 0;
    let totalCeilPaintSum = 0;
    let totalWallPaintSum = 0;
    let totalTapeSum = 0;
    let totalOpeningsCount = 0;
    
    state.rooms.forEach(room => {
        const hash = getRoomHash(room.vertices);
        const settings = state.roomSettings[hash] || { name: room.name, paintWalls: true, paintCeiling: true };
        const paintWalls = settings.paintWalls !== false;
        const paintCeiling = settings.paintCeiling !== false;
        
        // 1. Ceiling area and paint
        const ceilArea = room.area;
        const ceilPaint = paintCeiling ? (ceilArea / state.paintCoverage) * state.ceilingCoats * wasteMultiplier : 0;
        
        // 2. Wall paint calculations
        let roomWallLength = 0;
        let windowAreaTotal = 0;
        let doorAreaTotal = 0;
        let maskingTapeLength = 0;
        const openingsSummary = [];
        
        // Accumulate details for all walls enclosing this room
        room.walls.forEach(w => {
            const v1 = findVertex(w.v1Id);
            const v2 = findVertex(w.v2Id);
            const len = Math.hypot(v2.x - v1.x, v2.y - v1.y);
            roomWallLength += len;
            
            // Masking floor perimeter
            if (paintWalls) {
                maskingTapeLength += len;
            }
            
            // Find openings on this wall
            const wallOpenings = state.openings.filter(op => op.wallId === w.id);
            wallOpenings.forEach(op => {
                const opArea = op.width * op.height;
                totalOpeningsCount++;
                
                if (op.type === 'window') {
                    if (paintWalls) {
                        windowAreaTotal += opArea;
                        // Masking tape: 2 * (w + h)
                        maskingTapeLength += 2 * (op.width + op.height);
                    }
                    openingsSummary.push(`Win(${op.width}x${op.height})`);
                } else if (op.type === 'door') {
                    if (paintWalls) {
                        doorAreaTotal += opArea;
                        // Deduct door width from baseboard floor masking
                        maskingTapeLength -= op.width;
                        // Masking door trim: w + 2*h
                        maskingTapeLength += (op.width + 2 * op.height);
                    }
                    openingsSummary.push(`Door(${op.width}x${op.height})`);
                }
            });
        });
        
        // Gross Wall Area = wall perim * room height
        const grossWallArea = paintWalls ? roomWallLength * state.globalWallHeight : 0;
        
        // Net paintable wall area (doors are painted so we don't subtract them, windows are not)
        const netWallArea = paintWalls ? Math.max(0, grossWallArea - windowAreaTotal) : 0;
        
        const wallPaint = paintWalls ? (netWallArea / state.paintCoverage) * state.wallCoats * wasteMultiplier : 0;
        
        // Accumulate project totals
        totalCeilAreaSum += (paintCeiling ? ceilArea : 0);
        totalWallAreaSum += netWallArea;
        totalCeilPaintSum += ceilPaint;
        totalWallPaintSum += wallPaint;
        totalTapeSum += (paintWalls ? maskingTapeLength : 0);
        
        // Create table row
        const tr = document.createElement('tr');
        tr.innerHTML = `
            <td><strong>${settings.name || room.name}</strong></td>
            <td>${paintCeiling ? `${ceilArea.toFixed(2)} m²` : 'No Paint'}</td>
            <td>${paintWalls ? `${netWallArea.toFixed(2)} m²` : 'No Paint'}</td>
            <td>${paintCeiling ? `${ceilPaint.toFixed(1)} L` : '0.0 L'}</td>
            <td>${paintWalls ? `${wallPaint.toFixed(1)} L` : '0.0 L'}</td>
            <td>${paintWalls ? `${maskingTapeLength.toFixed(1)} m` : '0.0 m'}</td>
            <td>${openingsSummary.join(', ') || 'None'}</td>
        `;
        tableBody.appendChild(tr);
    });
    
    // Append Exterior row to breakdown table if exterior walls exist
    if (totalExtWallLength > 0) {
        const tr = document.createElement('tr');
        tr.style.background = 'rgba(6, 182, 212, 0.05)'; // Cyan tint to demarcate exterior wall row
        tr.innerHTML = `
            <td><strong>Exterior Walls</strong></td>
            <td>No Ceiling</td>
            <td>${netExtArea.toFixed(2)} m²</td>
            <td>0.0 L</td>
            <td>${extPaint.toFixed(1)} L</td>
            <td>0.0 m</td>
            <td>${extWindowsSummary.join(', ') || 'None'}</td>
        `;
        tableBody.appendChild(tr);
    }
    
    // Append Window row to breakdown table if windows exist
    if (totalWindowTrimArea > 0) {
        const tr = document.createElement('tr');
        tr.style.background = 'rgba(234, 88, 12, 0.04)'; // Subtle orange tint to match window trims
        tr.innerHTML = `
            <td><strong>Window Frame Trim</strong></td>
            <td>No Ceiling</td>
            <td>${totalWindowTrimArea.toFixed(2)} m²</td>
            <td>0.0 L</td>
            <td>${windowPaint.toFixed(1)} L</td>
            <td>0.0 m</td>
            <td>${windowDetails.join(', ') || 'None'}</td>
        `;
        tableBody.appendChild(tr);
    }
    
    // Render Summary Cards Block
    const totalsBlock = document.getElementById('dashboard-totals-block');
    if (totalsBlock) {
        let totalExtTape = 0;
        state.walls.forEach(w => {
            if (w.type && w.type.startsWith('exterior')) {
                const wallWindows = state.openings.filter(op => op.wallId === w.id && op.type === 'window');
                wallWindows.forEach(op => {
                    totalExtTape += 2 * (op.width + op.height);
                });
            }
        });

        totalsBlock.innerHTML = `
            <div class="total-card">
                <span class="lbl">Wall Paint</span>
                <span class="val">${totalWallPaintSum.toFixed(1)}<span class="unit-s"> L</span></span>
                <span class="sub">${totalWallAreaSum.toFixed(1)} m² (${state.wallCoats} coats)</span>
            </div>
            <div class="total-card">
                <span class="lbl">Ceiling Paint</span>
                <span class="val">${totalCeilPaintSum.toFixed(1)}<span class="unit-s"> L</span></span>
                <span class="sub">${totalCeilAreaSum.toFixed(1)} m² (${state.ceilingCoats} coats)</span>
            </div>
            <div class="total-card">
                <span class="lbl">Masking Tape Inside</span>
                <span class="val">${totalTapeSum.toFixed(1)}<span class="unit-s"> m</span></span>
                <span class="sub">(Rooms & Openings)</span>
            </div>
            <div class="total-card">
                <span class="lbl">Masking Tape Outside</span>
                <span class="val">${totalExtTape.toFixed(1)}<span class="unit-s"> m</span></span>
                <span class="sub">(Around each window)</span>
            </div>
            <div class="total-card">
                <span class="lbl">Windows Paint</span>
                <span class="val">${windowPaint.toFixed(1)}<span class="unit-s"> L</span></span>
                <span class="sub">${totalWindowTrimArea.toFixed(1)} m² (${state.wallCoats} coats)</span>
            </div>
            <div class="total-card">
                <span class="lbl">Exterior Paint</span>
                <span class="val">${extPaint.toFixed(1)}<span class="unit-s"> L</span></span>
                <span class="sub">${netExtArea.toFixed(1)} m² (${state.wallCoats} coats)</span>
            </div>
        `;
    }
    
    // Accumulate project totals in state for print block
    state.totalWallPaint = totalWallPaintSum;
    state.totalCeilPaint = totalCeilPaintSum;
    state.totalTape = totalTapeSum;
    state.totalWindowPaint = windowPaint;
    state.totalExteriorPaint = extPaint;
    state.totalWallArea = totalWallAreaSum;
    state.totalCeilArea = totalCeilAreaSum;
    state.totalWindowArea = totalWindowTrimArea;
    state.totalExteriorArea = netExtArea;

    // Update Totals Sidebar Card
    updateGrandTotals(totalWallPaintSum, totalCeilPaintSum, totalTapeSum, totalWallAreaSum, totalCeilAreaSum, totalOpeningsCount, extPaint, netExtArea, windowPaint, totalWindowTrimArea);
}

function updateGrandTotals(wallL, ceilL, tapeM, wallA, ceilA, openCount, extWallL, extWallA, winL, winA) {
    document.getElementById('total-wall-paint').innerHTML = `${wallL.toFixed(1)} <span class="unit-s">L</span>`;
    document.getElementById('total-ceil-paint').innerHTML = `${ceilL.toFixed(1)} <span class="unit-s">L</span>`;
    document.getElementById('total-tape').innerHTML = `${tapeM.toFixed(1)} <span class="unit-s">m</span>`;
    
    document.getElementById('total-wall-area').innerText = `${wallA.toFixed(1)} m² (${state.wallCoats} coats)`;
    document.getElementById('total-ceil-area').innerText = `${ceilA.toFixed(1)} m² (${state.ceilingCoats} coats)`;
    document.getElementById('total-openings-count').innerText = `${openCount} Openings`;
    
    // Window Totals
    document.getElementById('total-window-paint').innerHTML = `${winL.toFixed(1)} <span class="unit-s">L</span>`;
    document.getElementById('total-window-area').innerText = `${winA.toFixed(1)} m² (${state.wallCoats} coats)`;
    
    // Exterior Totals
    document.getElementById('total-ext-paint').innerHTML = `${extWallL.toFixed(1)} <span class="unit-s">L</span>`;
    document.getElementById('total-ext-area').innerText = `${extWallA.toFixed(1)} m² (${state.wallCoats} coats)`;
}

// --- 2D Drawing Engine ---
function draw() {
    ctx2D.clearRect(0, 0, canvas2D.width, canvas2D.height);
    
    // Draw Grid
    drawGrid();
    
    // Draw Print/Page Outline Sheet Guides
    drawPageSizeGuide();
    
    // Draw Rooms (Fill Areas)
    drawRoomFills();
    
    // Draw Walls
    drawWalls2D();
    
    // Draw Doors and Windows
    drawOpenings2D();
    
    // Draw active drawing template
    drawActiveDrawingLine();
    
    // Draw smart alignment guides
    drawSmartGuides();
    
    // Draw snaps indicators
    drawSnapIndicator();
    
    // Draw dragging angle arc
    drawDraggingAngleArc();
    
    // Draw corner angles for selected wall
    if (state.selectedElement && state.selectedElement.type === 'wall') {
        const wall = findWall(state.selectedElement.id);
        drawCornerAngles(wall);
    }
}

function drawGrid() {
    if (state.isPrinting) return; // Hide grid from prints
    const w = canvas2D.width;
    const h = canvas2D.height;
    
    // Grid colors
    const majorColor = state.isPrinting ? 'rgba(0, 0, 0, 0.06)' : 'rgba(255, 255, 255, 0.06)';
    const minorColor = state.isPrinting ? 'rgba(0, 0, 0, 0.02)' : 'rgba(255, 255, 255, 0.02)';
    
    const startWorld = screenToWorld(0, 0);
    const endWorld = screenToWorld(w, h);
    
    // Grid snapping line limits
    const startX = Math.floor(startWorld.x / state.subGridSize) * state.subGridSize;
    const endX = Math.ceil(endWorld.x / state.subGridSize) * state.subGridSize;
    const startY = Math.floor(startWorld.y / state.subGridSize) * state.subGridSize;
    const endY = Math.ceil(endWorld.y / state.subGridSize) * state.subGridSize;
    
    ctx2D.lineWidth = 1;
    
    // Draw minor subgrid lines
    if (state.zoom > 18) {
        ctx2D.strokeStyle = minorColor;
        ctx2D.beginPath();
        for (let x = startX; x <= endX; x += state.subGridSize) {
            if (Math.abs(Math.round(x) - x) < 0.01) continue; // Skip major axis line
            const s = worldToScreen(x, 0);
            ctx2D.moveTo(s.x, 0);
            ctx2D.lineTo(s.x, h);
        }
        for (let y = startY; y <= endY; y += state.subGridSize) {
            if (Math.abs(Math.round(y) - y) < 0.01) continue; // Skip major axis line
            const s = worldToScreen(0, y);
            ctx2D.moveTo(0, s.y);
            ctx2D.lineTo(w, s.y);
        }
        ctx2D.stroke();
    }
    
    // Draw major grid lines (1m intervals)
    ctx2D.strokeStyle = majorColor;
    ctx2D.beginPath();
    for (let x = Math.floor(startX); x <= Math.ceil(endX); x += state.gridSize) {
        const s = worldToScreen(x, 0);
        ctx2D.moveTo(s.x, 0);
        ctx2D.lineTo(s.x, h);
    }
    for (let y = Math.floor(startY); y <= Math.ceil(endY); y += state.gridSize) {
        const s = worldToScreen(0, y);
        ctx2D.moveTo(0, s.y);
        ctx2D.lineTo(w, s.y);
    }
    ctx2D.stroke();
    
    // Draw origin axes
    const origin = worldToScreen(0, 0);
    ctx2D.strokeStyle = state.isPrinting ? 'rgba(0, 0, 0, 0.15)' : 'rgba(255, 255, 255, 0.12)';
    ctx2D.lineWidth = 1.5;
    ctx2D.beginPath();
    ctx2D.moveTo(origin.x, 0);
    ctx2D.lineTo(origin.x, h);
    ctx2D.moveTo(0, origin.y);
    ctx2D.lineTo(w, origin.y);
    ctx2D.stroke();
}

function drawPageSizeGuide() {
    if (state.pageSizeGuide === 'none' || state.isPrinting) return;
    
    // Paper dimensions in meters at scale 1:50
    // A4: 297mm x 210mm => 14.85m x 10.50m
    // A3: 420mm x 297mm => 21.00m x 14.85m
    let pW, pH, scaleText;
    switch (state.pageSizeGuide) {
        case 'a4-portrait': pW = 10.50; pH = 14.85; scaleText = '1:50'; break;
        case 'a4-landscape': pW = 14.85; pH = 10.50; scaleText = '1:50'; break;
        case 'a3-portrait': pW = 14.85; pH = 21.00; scaleText = '1:50'; break;
        case 'a3-landscape': pW = 21.00; pH = 14.85; scaleText = '1:50'; break;
        case 'a4-portrait-100': pW = 21.00; pH = 29.70; scaleText = '1:100'; break;
        case 'a4-landscape-100': pW = 29.70; pH = 21.00; scaleText = '1:100'; break;
        case 'a3-portrait-100': pW = 29.70; pH = 42.00; scaleText = '1:100'; break;
        case 'a3-landscape-100': pW = 42.00; pH = 29.70; scaleText = '1:100'; break;
        default: return;
    }
    
    // Draw sheet box (centered at state.pagePos, which is origin by default)
    const topLeft = worldToScreen(state.pagePos.x - pW/2, state.pagePos.y - pH/2);
    const szX = pW * state.zoom;
    const szY = pH * state.zoom;
    
    // Draw dashed layout sheet guide
    ctx2D.strokeStyle = 'rgba(99, 102, 241, 0.35)';
    ctx2D.lineWidth = 2;
    ctx2D.setLineDash([10, 5]);
    ctx2D.strokeRect(topLeft.x, topLeft.y, szX, szY);
    ctx2D.setLineDash([]);
    
    // Sheet tag Label
    ctx2D.fillStyle = 'rgba(99, 102, 241, 0.5)';
    ctx2D.font = '10px Outfit, sans-serif';
    ctx2D.fillText(`${state.pageSizeGuide.split('-')[0].toUpperCase()} ${state.pageSizeGuide.split('-')[1].toUpperCase()} SHEET OUTLINE (${scaleText} SCALE)`, topLeft.x + 10, topLeft.y + 20);
}

function drawRoomFills() {
    state.rooms.forEach(room => {
        ctx2D.beginPath();
        const startV = findVertex(room.vertices[0]);
        if (!startV) return;
        
        const startScr = worldToScreen(startV.x, startV.y);
        ctx2D.moveTo(startScr.x, startScr.y);
        
        for (let i = 1; i < room.vertices.length; i++) {
            const v = findVertex(room.vertices[i]);
            const s = worldToScreen(v.x, v.y);
            ctx2D.lineTo(s.x, s.y);
        }
        ctx2D.closePath();
        
        const isSelected = state.selectedElement && state.selectedElement.type === 'room' && state.selectedElement.id === room.id;
        
        // Translucent room glow fill
        if (state.isPrinting) {
            ctx2D.fillStyle = 'rgba(99, 102, 241, 0.01)';
        } else if (isSelected) {
            ctx2D.fillStyle = 'rgba(250, 204, 21, 0.12)';
        } else {
            ctx2D.fillStyle = 'rgba(99, 102, 241, 0.04)';
        }
        ctx2D.fill();
        
        // Calculate centroid to draw labels
        let sumX = 0, sumY = 0;
        room.vertices.forEach(vId => {
            const v = findVertex(vId);
            sumX += v.x;
            sumY += v.y;
        });
        const cx = sumX / room.vertices.length;
        const cy = sumY / room.vertices.length;
        
        const textPos = worldToScreen(cx, cy);
        
        const hash = getRoomHash(room.vertices);
        const settings = state.roomSettings[hash] || { name: room.name, paintWalls: true, paintCeiling: true };
        const paintWalls = settings.paintWalls !== false;
        const paintCeiling = settings.paintCeiling !== false;
        
        // Draw Room Name & Area
        ctx2D.fillStyle = state.isPrinting ? '#1f2937' : (isSelected ? '#facc15' : '#a5b4fc');
        ctx2D.font = state.isPrinting ? 'bold 15px Outfit, sans-serif' : 'bold 12px Outfit, sans-serif';
        ctx2D.textAlign = 'center';
        ctx2D.textBaseline = 'middle';
        ctx2D.fillText(settings.name || room.name, textPos.x, textPos.y - (state.isPrinting ? 11 : 8));
        
        ctx2D.fillStyle = state.isPrinting ? '#4b5563' : 'rgba(255, 255, 255, 0.7)';
        ctx2D.font = state.isPrinting ? 'bold 13px Outfit, sans-serif' : '11px Outfit, sans-serif';
        
        let subText = `${room.area.toFixed(2)} m²`;
        if (!paintWalls && !paintCeiling) {
            subText += ` (No Paint)`;
        } else if (!paintWalls) {
            subText += ` (No Wall Paint)`;
        } else if (!paintCeiling) {
            subText += ` (No Ceiling Paint)`;
        }
        ctx2D.fillText(subText, textPos.x, textPos.y + (state.isPrinting ? 11 : 8));
    });
}

function drawWalls2D() {
    state.walls.forEach(w => {
        const v1 = findVertex(w.v1Id);
        const v2 = findVertex(w.v2Id);
        if (!v1 || !v2) return;
        
        const s1 = worldToScreen(v1.x, v1.y);
        const s2 = worldToScreen(v2.x, v2.y);
        
        const len = Math.hypot(v2.x - v1.x, v2.y - v1.y);
        const angle = Math.atan2(v2.y - v1.y, v2.x - v1.x);
        
        // 1. Draw wall thick polygon block with miter joints at corners
        const joint1 = getWallJointPoints(w.id, w.v1Id);
        const joint2 = getWallJointPoints(w.id, w.v2Id);
        if (!joint1 || !joint2) return;
        
        const thickPx = w.thickness * state.zoom;
        const s1Left = worldToScreen(joint1.left.x, joint1.left.y);
        const s1Right = worldToScreen(joint1.right.x, joint1.right.y);
        const s2Left = worldToScreen(joint2.left.x, joint2.left.y);
        const s2Right = worldToScreen(joint2.right.x, joint2.right.y);
        
        ctx2D.beginPath();
        ctx2D.moveTo(s1Left.x, s1Left.y);
        ctx2D.lineTo(s2Right.x, s2Right.y); // Left side boundary
        ctx2D.lineTo(s2Left.x, s2Left.y);   // Flat cap at V2
        ctx2D.lineTo(s1Right.x, s1Right.y); // Right side boundary
        ctx2D.closePath();
        
        // Colors base on selection
        const isSelected = state.selectedElement && state.selectedElement.type === 'wall' && state.selectedElement.id === w.id;
        
        if (isSelected) {
            ctx2D.fillStyle = 'rgba(99, 102, 241, 0.18)'; // active indigo glow
            ctx2D.strokeStyle = '#6366f1';
            ctx2D.lineWidth = 2;
        } else {
            ctx2D.fillStyle = state.isPrinting ? 'rgba(0, 0, 0, 0.12)' : 'rgba(255, 255, 255, 0.08)'; // normal wall fill
            ctx2D.strokeStyle = state.isPrinting ? 'rgba(0, 0, 0, 0.8)' : 'rgba(255, 255, 255, 0.3)';
            ctx2D.lineWidth = state.isPrinting ? 1.8 : 1.2;
        }
        ctx2D.fill();
        ctx2D.stroke();
        
        // Draw centerline
        if (!state.isPrinting) {
            ctx2D.strokeStyle = 'rgba(255, 255, 255, 0.15)';
            ctx2D.lineWidth = 0.8;
            ctx2D.beginPath();
            ctx2D.moveTo(s1.x, s1.y);
            ctx2D.lineTo(s2.x, s2.y);
            ctx2D.stroke();
        }
        
        // 2. Draw wall length labels
        const midX = (s1.x + s2.x) / 2;
        const midY = (s1.y + s2.y) / 2;
        
        ctx2D.save();
        ctx2D.translate(midX, midY);
        // Rotate text to align along wall angle (prevent upside-down text)
        let textAngle = angle;
        if (angle > Math.PI / 2 || angle < -Math.PI / 2) {
            textAngle += Math.PI;
        }
        ctx2D.rotate(textAngle);
        
        ctx2D.fillStyle = state.isPrinting ? '#000000' : '#f3f4f6';
        ctx2D.font = state.isPrinting ? 'bold 14px Outfit, sans-serif' : '600 11px Outfit, sans-serif';
        ctx2D.textAlign = 'center';
        ctx2D.textBaseline = 'bottom';
        // Offset text above the wall line
        ctx2D.fillText(`${len.toFixed(2)} m`, 0, -thickPx/2 - (state.isPrinting ? 6 : 4));
        ctx2D.restore();
        
        // 3. Draw Vertex Handles A & B if selected
        if (isSelected) {
            const handleRadius = 9;
            
            // Handle A (Start Point) - Green if locked, dark gray if unlocked
            ctx2D.fillStyle = state.lockedVertexId === v1.id ? '#10b981' : '#4b5563';
            ctx2D.strokeStyle = 'white';
            ctx2D.lineWidth = 1.5;
            ctx2D.beginPath();
            ctx2D.arc(s1.x, s1.y, handleRadius, 0, Math.PI * 2);
            ctx2D.fill();
            ctx2D.stroke();
            
            ctx2D.fillStyle = 'white';
            ctx2D.font = 'bold 9px Outfit, sans-serif';
            ctx2D.textAlign = 'center';
            ctx2D.textBaseline = 'middle';
            ctx2D.fillText('A', s1.x, s1.y);
            
            // Handle B (End Point) - Green if locked, dark gray if unlocked
            ctx2D.fillStyle = state.lockedVertexId === v2.id ? '#10b981' : '#4b5563';
            ctx2D.beginPath();
            ctx2D.arc(s2.x, s2.y, handleRadius, 0, Math.PI * 2);
            ctx2D.fill();
            ctx2D.stroke();
            
            ctx2D.fillStyle = 'white';
            ctx2D.font = 'bold 9px Outfit, sans-serif';
            ctx2D.textAlign = 'center';
            ctx2D.textBaseline = 'middle';
            ctx2D.fillText('B', s2.x, s2.y);
        }
    });
}

function drawOpenings2D() {
    state.openings.forEach(op => {
        const wall = findWall(op.wallId);
        if (!wall) return;
        
        const v1 = findVertex(wall.v1Id);
        const v2 = findVertex(wall.v2Id);
        if (!v1 || !v2) return;
        
        const angle = Math.atan2(v2.y - v1.y, v2.x - v1.x);
        
        // Start coords of opening
        const opStartX = v1.x + op.offset * Math.cos(angle);
        const opStartY = v1.y + op.offset * Math.sin(angle);
        
        // End coords of opening
        const opEndX = opStartX + op.width * Math.cos(angle);
        const opEndY = opStartY + op.width * Math.sin(angle);
        
        const sStart = worldToScreen(opStartX, opStartY);
        const sEnd = worldToScreen(opEndX, opEndY);
        
        const isSelected = state.selectedElement && state.selectedElement.type === 'opening' && state.selectedElement.id === op.id;
        
        // Window vs Door symbols
        if (op.type === 'window') {
            // Yellow highlight if selected, blue glass colored block otherwise
            ctx2D.strokeStyle = isSelected ? '#facc15' : (state.isPrinting ? '#0891b2' : '#22d3ee');
            ctx2D.fillStyle = isSelected ? 'rgba(250, 204, 21, 0.25)' : (state.isPrinting ? 'rgba(8, 145, 178, 0.08)' : 'rgba(34, 211, 238, 0.15)');
            ctx2D.lineWidth = isSelected ? 2.5 : 1.5;
            
            // Draw window rectangles
            const dx = sEnd.x - sStart.x;
            const dy = sEnd.y - sStart.y;
            const wLenPx = Math.hypot(dx, dy);
            
            ctx2D.save();
            ctx2D.translate(sStart.x, sStart.y);
            ctx2D.rotate(angle);
            
            const wallThPx = wall.thickness * state.zoom;
            ctx2D.fillRect(0, -wallThPx/2, wLenPx, wallThPx);
            ctx2D.strokeRect(0, -wallThPx/2, wLenPx, wallThPx);
            
            // Draw double glass line
            ctx2D.beginPath();
            ctx2D.moveTo(0, 0);
            ctx2D.lineTo(wLenPx, 0);
            ctx2D.strokeStyle = state.isPrinting ? '#0891b2' : '#fff';
            ctx2D.stroke();
            
            ctx2D.restore();
        } 
        
        else if (op.type === 'door') {
            // Yellow highlight if selected, purple swing otherwise (or dark purple for print)
            ctx2D.strokeStyle = isSelected ? '#facc15' : (state.isPrinting ? '#86198f' : '#a855f7');
            ctx2D.lineWidth = isSelected ? 2.5 : 1.5;
            
            const dx = sEnd.x - sStart.x;
            const dy = sEnd.y - sStart.y;
            const wLenPx = Math.hypot(dx, dy);
            
            ctx2D.save();
            ctx2D.translate(sStart.x, sStart.y);
            ctx2D.rotate(angle);
            
            const hingeSide = op.hingeSide || 'left';
            const swingDir = op.swingDir || 'out';
            
            ctx2D.beginPath();
            if (hingeSide === 'left') {
                // Hinge at Left (0, 0)
                if (swingDir === 'out') {
                    // Swing leaf
                    ctx2D.moveTo(0, 0);
                    ctx2D.lineTo(0, -wLenPx);
                    ctx2D.stroke();
                    
                    // Swing arc
                    ctx2D.setLineDash([3, 3]);
                    ctx2D.beginPath();
                    ctx2D.arc(0, 0, wLenPx, -Math.PI / 2, 0, false);
                    ctx2D.stroke();
                } else {
                    // Swing leaf (inward)
                    ctx2D.moveTo(0, 0);
                    ctx2D.lineTo(0, wLenPx);
                    ctx2D.stroke();
                    
                    // Swing arc
                    ctx2D.setLineDash([3, 3]);
                    ctx2D.beginPath();
                    ctx2D.arc(0, 0, wLenPx, Math.PI / 2, 0, true);
                    ctx2D.stroke();
                }
            } else {
                // Hinge at Right (wLenPx, 0)
                if (swingDir === 'out') {
                    // Swing leaf
                    ctx2D.moveTo(wLenPx, 0);
                    ctx2D.lineTo(wLenPx, -wLenPx);
                    ctx2D.stroke();
                    
                    // Swing arc
                    ctx2D.setLineDash([3, 3]);
                    ctx2D.beginPath();
                    ctx2D.arc(wLenPx, 0, wLenPx, -Math.PI / 2, Math.PI, true);
                    ctx2D.stroke();
                } else {
                    // Swing leaf (inward)
                    ctx2D.moveTo(wLenPx, 0);
                    ctx2D.lineTo(wLenPx, wLenPx);
                    ctx2D.stroke();
                    
                    // Swing arc
                    ctx2D.setLineDash([3, 3]);
                    ctx2D.beginPath();
                    ctx2D.arc(wLenPx, 0, wLenPx, Math.PI / 2, Math.PI, false);
                    ctx2D.stroke();
                }
            }
            ctx2D.setLineDash([]);
            ctx2D.restore();
        }
        
        // Draw dimension lines on either side of the window/door when selected or dragged
        const isDragging = activeDragOpeningId === op.id;
        if (isSelected || isDragging) {
            drawOpeningDimensionLines(op, v1, v2, opStartX, opStartY, opEndX, opEndY, angle);
        }
    });
}

function drawOpeningDimensionLines(op, v1, v2, opStartX, opStartY, opEndX, opEndY, angle) {
    const wall = findWall(op.wallId);
    if (!wall) return;
    
    // Normal vector pointing "up" relative to wall direction
    const norm = { x: -Math.sin(angle), y: Math.cos(angle) };
    
    // Right face coordinates in world space (inside measurement)
    const joint1 = getWallJointPoints(wall.id, wall.v1Id);
    const joint2 = getWallJointPoints(wall.id, wall.v2Id);
    
    const rightFaceV1 = joint1 ? joint1.right : { x: v1.x - (wall.thickness/2) * norm.x, y: v1.y - (wall.thickness/2) * norm.y };
    const rightFaceV2 = joint2 ? joint2.left : { x: v2.x - (wall.thickness/2) * norm.x, y: v2.y - (wall.thickness/2) * norm.y };
    
    const rightFaceStart = { x: opStartX - (wall.thickness/2) * norm.x, y: opStartY - (wall.thickness/2) * norm.y };
    const rightFaceEnd = { x: opEndX - (wall.thickness/2) * norm.x, y: opEndY - (wall.thickness/2) * norm.y };
    
    // Convert to screen space
    const s1 = worldToScreen(rightFaceV1.x, rightFaceV1.y);
    const sStart = worldToScreen(rightFaceStart.x, rightFaceStart.y);
    const sEnd = worldToScreen(rightFaceEnd.x, rightFaceEnd.y);
    const s2 = worldToScreen(rightFaceV2.x, rightFaceV2.y);
    
    // Offset by 16px along negative normal (inside of the wall) for the dimension line
    const offsetPx = 16;
    const p1 = { x: s1.x - offsetPx * norm.x, y: s1.y - offsetPx * norm.y };
    const pStart = { x: sStart.x - offsetPx * norm.x, y: sStart.y - offsetPx * norm.y };
    const pEnd = { x: sEnd.x - offsetPx * norm.x, y: sEnd.y - offsetPx * norm.y };
    const p2 = { x: s2.x - offsetPx * norm.x, y: s2.y - offsetPx * norm.y };
    
    // Physical distances along inside face
    const leftLen = Math.max(0, Math.hypot(rightFaceStart.x - rightFaceV1.x, rightFaceStart.y - rightFaceV1.y));
    const rightLen = Math.max(0, Math.hypot(rightFaceV2.x - rightFaceEnd.x, rightFaceV2.y - rightFaceEnd.y));
    
    ctx2D.save();
    ctx2D.strokeStyle = state.isPrinting ? 'rgba(8, 145, 178, 0.8)' : 'rgba(6, 182, 212, 0.7)'; // Cyan dimension guides
    ctx2D.lineWidth = 1;
    ctx2D.fillStyle = state.isPrinting ? '#0891b2' : '#06b6d4';
    ctx2D.font = state.isPrinting ? 'bold 12px Outfit, sans-serif' : '500 10px Outfit, sans-serif';
    ctx2D.textAlign = 'center';
    ctx2D.textBaseline = 'middle';
    
    // Helper to draw a dimension segment with ticks and text
    function drawDimSeg(ptA, ptB, value) {
        if (value < 0.01) return;
        
        // Draw main dimension line
        ctx2D.beginPath();
        ctx2D.moveTo(ptA.x, ptA.y);
        ctx2D.lineTo(ptB.x, ptB.y);
        ctx2D.stroke();
        
        // Draw tick marks at A and B
        const tickLen = 4;
        
        // Draw tick A
        ctx2D.beginPath();
        ctx2D.moveTo(ptA.x - tickLen * norm.x, ptA.y - tickLen * norm.y);
        ctx2D.lineTo(ptA.x + tickLen * norm.x, ptA.y + tickLen * norm.y);
        ctx2D.stroke();
        
        // Draw tick B
        ctx2D.beginPath();
        ctx2D.moveTo(ptB.x - tickLen * norm.x, ptB.y - tickLen * norm.y);
        ctx2D.lineTo(ptB.x + tickLen * norm.x, ptB.y + tickLen * norm.y);
        ctx2D.stroke();
        
        // Draw value text centered
        const midX = (ptA.x + ptB.x) / 2;
        const midY = (ptA.y + ptB.y) / 2;
        
        // Clear background for text using a small capsule
        ctx2D.save();
        ctx2D.translate(midX, midY);
        // Rotate text along wall angle
        let textAngle = angle;
        if (angle > Math.PI / 2 || angle < -Math.PI / 2) textAngle += Math.PI;
        ctx2D.rotate(textAngle);
        
        // Background capsule
        ctx2D.fillStyle = state.isPrinting ? '#ffffff' : 'rgba(15, 15, 25, 0.95)';
        ctx2D.strokeStyle = state.isPrinting ? 'rgba(8, 145, 178, 0.5)' : 'rgba(6, 182, 212, 0.4)';
        ctx2D.lineWidth = 1;
        ctx2D.beginPath();
        const textW = ctx2D.measureText(`${value.toFixed(2)} m`).width + 10;
        ctx2D.roundRect(-textW/2, state.isPrinting ? -9 : -7, textW, state.isPrinting ? 18 : 14, 3);
        ctx2D.fill();
        ctx2D.stroke();
        
        ctx2D.fillStyle = state.isPrinting ? '#0891b2' : '#22d3ee';
        ctx2D.fillText(`${value.toFixed(2)} m`, 0, 0);
        ctx2D.restore();
    }
    
    // Draw extension projection lines from wall to dimension line
    ctx2D.strokeStyle = state.isPrinting ? 'rgba(0, 0, 0, 0.15)' : 'rgba(255, 255, 255, 0.15)';
    ctx2D.beginPath();
    ctx2D.moveTo(s1.x, s1.y);
    ctx2D.lineTo(p1.x, p1.y);
    ctx2D.moveTo(sStart.x, sStart.y);
    ctx2D.lineTo(pStart.x, pStart.y);
    ctx2D.moveTo(sEnd.x, sEnd.y);
    ctx2D.lineTo(pEnd.x, pEnd.y);
    ctx2D.moveTo(s2.x, s2.y);
    ctx2D.lineTo(p2.x, p2.y);
    ctx2D.stroke();
    
    // Draw segments
    drawDimSeg(p1, pStart, leftLen);
    drawDimSeg(pStart, pEnd, op.width);
    drawDimSeg(pEnd, p2, rightLen);
    
    ctx2D.restore();
}

function drawActiveDrawingLine() {
    if (state.activeTool === 'wall' && state.drawingStartVertexId && state.tempWallEnd) {
        const startV = findVertex(state.drawingStartVertexId);
        const sStart = worldToScreen(startV.x, startV.y);
        const sEnd = worldToScreen(state.tempWallEnd.x, state.tempWallEnd.y);
        
        ctx2D.strokeStyle = 'rgba(6, 182, 212, 0.6)'; // cyan active preview line
        ctx2D.lineWidth = 1.5;
        ctx2D.setLineDash([5, 5]);
        
        ctx2D.beginPath();
        ctx2D.moveTo(sStart.x, sStart.y);
        ctx2D.lineTo(sEnd.x, sEnd.y);
        ctx2D.stroke();
        ctx2D.setLineDash([]);
        
        // Draw distance tag
        const dist = Math.hypot(state.tempWallEnd.x - startV.x, state.tempWallEnd.y - startV.y);
        ctx2D.fillStyle = 'rgba(6, 182, 212, 0.9)';
        ctx2D.font = 'bold 10px Outfit, sans-serif';
        ctx2D.fillText(`${dist.toFixed(2)} m`, (sStart.x + sEnd.x) / 2, (sStart.y + sEnd.y) / 2 - 10);
        
        // Draw active angle arc
        drawAngleArc(startV, state.tempWallEnd);
    }
}

function drawAngleArc(ref, target) {
    if (!ref || !target) return;
    const sRef = worldToScreen(ref.x, ref.y);
    const sTarget = worldToScreen(target.x, target.y);
    
    const dx = target.x - ref.x;
    const dy = target.y - ref.y;
    const distance = Math.hypot(dx, dy);
    if (distance < 0.05) return;
    
    let angle = Math.atan2(dy, dx);
    let deg = (angle * 180) / Math.PI;
    if (deg < 0) deg += 360;
    
    const arcRadius = 45;
    
    // Draw reference horizontal line in dashed gray
    ctx2D.strokeStyle = 'rgba(255, 255, 255, 0.25)';
    ctx2D.lineWidth = 1;
    ctx2D.setLineDash([3, 3]);
    ctx2D.beginPath();
    ctx2D.moveTo(sRef.x, sRef.y);
    ctx2D.lineTo(sRef.x + arcRadius + 15, sRef.y);
    ctx2D.stroke();
    ctx2D.setLineDash([]);
    
    // Draw cyan arc
    ctx2D.strokeStyle = 'rgba(6, 182, 212, 0.6)';
    ctx2D.lineWidth = 1.5;
    ctx2D.beginPath();
    ctx2D.arc(sRef.x, sRef.y, arcRadius, 0, angle, angle < 0);
    ctx2D.stroke();
    
    // Draw text tag
    ctx2D.fillStyle = '#06b6d4';
    ctx2D.font = '600 10px Outfit, sans-serif';
    ctx2D.textAlign = 'left';
    ctx2D.textBaseline = 'middle';
    
    // Place text tag slightly offset
    let midAngle = angle / 2;
    if (angle < 0) midAngle = (Math.PI * 2 + angle) / 2;
    const textX = sRef.x + (arcRadius + 10) * Math.cos(midAngle);
    const textY = sRef.y + (arcRadius + 10) * Math.sin(midAngle);
    
    ctx2D.fillText(`${deg.toFixed(1)}°`, textX, textY);
}

function drawDraggingAngleArc() {
    if (!activeDragVertexId) return;
    const draggedV = findVertex(activeDragVertexId);
    if (!draggedV) return;
    
    let refVertexId = null;
    if (state.selectedElement && state.selectedElement.type === 'wall') {
        const wall = findWall(state.selectedElement.id);
        if (wall.v1Id === activeDragVertexId) refVertexId = wall.v2Id;
        else if (wall.v2Id === activeDragVertexId) refVertexId = wall.v1Id;
    }
    if (!refVertexId) {
        const connWall = state.walls.find(w => w.v1Id === activeDragVertexId || w.v2Id === activeDragVertexId);
        if (connWall) {
            refVertexId = connWall.v1Id === activeDragVertexId ? connWall.v2Id : connWall.v1Id;
        }
    }
    if (refVertexId) {
        drawAngleArc(findVertex(refVertexId), draggedV);
    }
}

function drawSnapIndicator() {
    if (state.viewMode !== '2d' || !state.hoverX || !state.hoverY) return;
    
    if (state.activeTool === 'select' || state.activeTool === 'wall' || state.activeTool === 'door' || state.activeTool === 'window') {
        const excludeId = activeDragVertexId || state.drawingStartVertexId;
        const snap = getSnapPoint(state.hoverX, state.hoverY, excludeId);
        if (snap.type !== 'none') {
            const s = worldToScreen(snap.x, snap.y);
            ctx2D.fillStyle = snap.type === 'vertex' ? '#10b981' : '#6366f1';
            ctx2D.strokeStyle = 'white';
            ctx2D.lineWidth = 1.5;
            ctx2D.beginPath();
            ctx2D.arc(s.x, s.y, 6, 0, Math.PI * 2);
            ctx2D.fill();
            ctx2D.stroke();
        }
    }
}

function drawSmartGuides() {
    if (state.viewMode !== '2d' || !state.activeAlignments || state.activeAlignments.length === 0) return;
    
    ctx2D.save();
    ctx2D.strokeStyle = '#f43f5e'; // Coral red dashed guide line
    ctx2D.lineWidth = 1.5;
    ctx2D.setLineDash([6, 4]);
    
    state.activeAlignments.forEach(guide => {
        if (guide.type === 'horizontal') {
            const s1 = worldToScreen(guide.x1, guide.y);
            const s2 = worldToScreen(guide.x2, guide.y);
            
            ctx2D.beginPath();
            ctx2D.moveTo(s1.x, s1.y);
            ctx2D.lineTo(s2.x, s2.y);
            ctx2D.stroke();
            
            // Draw alignment target square box
            ctx2D.fillStyle = 'rgba(244, 63, 94, 0.15)';
            ctx2D.strokeStyle = '#f43f5e';
            ctx2D.setLineDash([]);
            ctx2D.lineWidth = 1;
            ctx2D.strokeRect(s2.x - 5, s2.y - 5, 10, 10);
            ctx2D.fillRect(s2.x - 5, s2.y - 5, 10, 10);
            ctx2D.setLineDash([6, 4]);
        } 
        
        else if (guide.type === 'vertical') {
            const s1 = worldToScreen(guide.x, guide.y1);
            const s2 = worldToScreen(guide.x, guide.y2);
            
            ctx2D.beginPath();
            ctx2D.moveTo(s1.x, s1.y);
            ctx2D.lineTo(s2.x, s2.y);
            ctx2D.stroke();
            
            // Draw alignment target square box
            ctx2D.fillStyle = 'rgba(244, 63, 94, 0.15)';
            ctx2D.strokeStyle = '#f43f5e';
            ctx2D.setLineDash([]);
            ctx2D.lineWidth = 1;
            ctx2D.strokeRect(s2.x - 5, s2.y - 5, 10, 10);
            ctx2D.fillRect(s2.x - 5, s2.y - 5, 10, 10);
            ctx2D.setLineDash([6, 4]);
        }
    });
    
    ctx2D.restore();
}

// Computes joint corner points (left & right) for a wall at a specific vertex.
// Resolves overlaps and creates clean miter joints with connected walls.
function getWallJointPoints(wallId, vertexId) {
    const wallObj = findWall(wallId);
    const v = findVertex(vertexId);
    if (!wallObj || !v) return null;
    
    const vOtherId = wallObj.v1Id === vertexId ? wallObj.v2Id : wallObj.v1Id;
    const vOther = findVertex(vOtherId);
    if (!vOther) return null;
    
    // Vector direction outgoing from vertexId
    const dx = vOther.x - v.x;
    const dy = vOther.y - v.y;
    const len = Math.hypot(dx, dy);
    if (len === 0) return null;
    
    const dir = { x: dx / len, y: dy / len };
    const norm = { x: -dir.y, y: dir.x };
    
    // Default flat cap offsets (if no joint)
    const t = wallObj.thickness;
    const defaultLeft = { x: v.x + (t / 2) * norm.x, y: v.y + (t / 2) * norm.y };
    const defaultRight = { x: v.x - (t / 2) * norm.x, y: v.y - (t / 2) * norm.y };
    
    // Find all walls connected to this vertex
    const connWalls = state.walls.filter(w => w.id !== wallId && (w.v1Id === vertexId || w.v2Id === vertexId));
    if (connWalls.length === 0) {
        // Dead end: simple flat cap
        return { left: defaultLeft, right: defaultRight };
    }
    
    // Calculate outgoing directions for all connected walls
    const wallDirections = [{
        id: wallId,
        wall: wallObj,
        dir: dir,
        norm: norm,
        angle: Math.atan2(dir.y, dir.x),
        thickness: t
    }];
    
    connWalls.forEach(w => {
        const otherVId = w.v1Id === vertexId ? w.v2Id : w.v1Id;
        const otherV = findVertex(otherVId);
        if (!otherV) return;
        const cDx = otherV.x - v.x;
        const cDy = otherV.y - v.y;
        const cLen = Math.hypot(cDx, cDy);
        if (cLen === 0) return;
        const cDir = { x: cDx / cLen, y: cDy / cLen };
        wallDirections.push({
            id: w.id,
            wall: w,
            dir: cDir,
            norm: { x: -cDir.y, y: cDir.x },
            angle: Math.atan2(cDy, cDx),
            thickness: w.thickness
        });
    });
    
    // Sort outgoing walls counter-clockwise by angle
    wallDirections.sort((a, b) => a.angle - b.angle);
    
    // Find our wall's sorted position
    const myIndex = wallDirections.findIndex(w => w.id === wallId);
    const N = wallDirections.length;
    
    // Counter-clockwise adjacent neighbor
    const ccwNeighbor = wallDirections[(myIndex + 1) % N];
    // Clockwise adjacent neighbor
    const cwNeighbor = wallDirections[(myIndex - 1 + N) % N];
    
    // Define helper to intersect offset lines
    function intersectOffsetLines(wA, sideA, wB, sideB) {
        // Offset lines:
        // Wall A offset line: (v + sideA * tA/2 * normA) + sA * dirA
        // Wall B offset line: (v + sideB * tB/2 * normB) + sB * dirB
        const offsetA = sideA * (wA.thickness / 2);
        const pA = { x: v.x + offsetA * wA.norm.x, y: v.y + offsetA * wA.norm.y };
        
        const offsetB = sideB * (wB.thickness / 2);
        const pB = { x: v.x + offsetB * wB.norm.x, y: v.y + offsetB * wB.norm.y };
        
        const pt = intersectLines(pA, wA.dir, pB, wB.dir);
        if (!pt) return null;
        
        // Miter Limit clamping: if intersection is too far away (sharp angle), limit it
        const dist = Math.hypot(pt.x - v.x, pt.y - v.y);
        const maxMiter = Math.max(wA.thickness, wB.thickness) * 2.5;
        if (dist > maxMiter) {
            // Project miter to limit distance
            const miterDirX = pt.x - v.x;
            const miterDirY = pt.y - v.y;
            return {
                x: v.x + (miterDirX / dist) * maxMiter,
                y: v.y + (miterDirY / dist) * maxMiter
            };
        }
        return pt;
    }
    
    // Helper line-line intersection
    function intersectLines(p1, dir1, p2, dir2) {
        const det = -dir1.x * dir2.y + dir1.y * dir2.x;
        if (Math.abs(det) < 1e-4) return null;
        const dx = p2.x - p1.x;
        const dy = p2.y - p1.y;
        const s = (-dx * dir2.y + dy * dir2.x) / det;
        return { x: p1.x + s * dir1.x, y: p1.y + s * dir1.y };
    }
    
    // T-Junction resolution override
    if (wallDirections.length === 3) {
        let collinearIdx1 = -1;
        let collinearIdx2 = -1;
        let branchIdx = -1;
        
        for (let i = 0; i < 3; i++) {
            for (let j = i + 1; j < 3; j++) {
                let diff = Math.abs(wallDirections[i].angle - wallDirections[j].angle);
                while (diff > Math.PI * 2) diff -= Math.PI * 2;
                if (diff > Math.PI) diff = Math.PI * 2 - diff;
                
                if (Math.abs(diff - Math.PI) < 0.35) {
                    collinearIdx1 = i;
                    collinearIdx2 = j;
                    branchIdx = 3 - (i + j);
                    break;
                }
            }
            if (collinearIdx1 !== -1) break;
        }
        
        if (collinearIdx1 !== -1) {
            const col1 = wallDirections[collinearIdx1];
            const col2 = wallDirections[collinearIdx2];
            const branch = wallDirections[branchIdx];
            
            if (myIndex === collinearIdx1 || myIndex === collinearIdx2) {
                const otherCol = myIndex === collinearIdx1 ? col2 : col1;
                let CCWJ = intersectOffsetLines(wallDirections[myIndex], 1, otherCol, -1) || defaultLeft;
                let CWJ = intersectOffsetLines(wallDirections[myIndex], -1, otherCol, 1) || defaultRight;
                return { left: CCWJ, right: CWJ };
            } else if (myIndex === branchIdx) {
                const tCol = col1.thickness;
                const vFace = {
                    x: v.x + branch.dir.x * (tCol / 2),
                    y: v.y + branch.dir.y * (tCol / 2)
                };
                
                const offsetBranchLeft = branch.thickness / 2;
                const pBranchLeft = {
                    x: v.x + offsetBranchLeft * branch.norm.x,
                    y: v.y + offsetBranchLeft * branch.norm.y
                };
                const jointLeft = intersectLines(pBranchLeft, branch.dir, vFace, col1.dir) || defaultLeft;
                
                const offsetBranchRight = -branch.thickness / 2;
                const pBranchRight = {
                    x: v.x + offsetBranchRight * branch.norm.x,
                    y: v.y + offsetBranchRight * branch.norm.y
                };
                const jointRight = intersectLines(pBranchRight, branch.dir, vFace, col1.dir) || defaultRight;
                
                return { left: jointLeft, right: jointRight };
            }
        }
    }

    // CCW Side of Wall A meets CW Side of Wall B (CCW Neighbor)
    let jointLeft = intersectOffsetLines(
        wallDirections[myIndex], 1, 
        ccwNeighbor, -1
    );
    if (!jointLeft) jointLeft = defaultLeft;
    
    // CW Side of Wall A meets CCW Side of Wall C (CW Neighbor)
    let jointRight = intersectOffsetLines(
        wallDirections[myIndex], -1, 
        cwNeighbor, 1
    );
    if (!jointRight) jointRight = defaultRight;
    
    return { left: jointLeft, right: jointRight };
}

// --- 3D Visualization Toggle Engine ---
function toggleViewMode(mode) {
    if (state.viewMode === mode) return;
    state.viewMode = mode;
    
    const btn2D = document.getElementById('btn-view-2d');
    const btn3D = document.getElementById('btn-view-3d');
    const btnMap = document.getElementById('btn-view-map');
    const container2D = document.getElementById('canvas-2d-container');
    const container3D = document.getElementById('canvas-3d-container');
    const containerMap = document.getElementById('canvas-map-container');
    const sidebarLocation = document.getElementById('sidebar-location-section');
    
    // Stop ThreeJS Loop if exiting 3D view
    if (state.three.animationFrameId) {
        cancelAnimationFrame(state.three.animationFrameId);
        state.three.animationFrameId = null;
    }
    
    // Update button states
    btn2D.classList.remove('active');
    btn3D.classList.remove('active');
    if (btnMap) btnMap.classList.remove('active');
    
    container2D.classList.add('hidden');
    container3D.classList.add('hidden');
    if (containerMap) containerMap.classList.add('hidden');
    if (sidebarLocation) sidebarLocation.classList.add('hidden');
    
    if (mode === '2d') {
        btn2D.classList.add('active');
        container2D.classList.remove('hidden');
        draw();
    } else if (mode === '3d') {
        btn3D.classList.add('active');
        container3D.classList.remove('hidden');
        if (state.show3DMap && sidebarLocation) {
            sidebarLocation.classList.remove('hidden');
        }
        initThreeJS();
    } else if (mode === 'map') {
        state.show3DMap = true; // Auto-enable 3D map background when map view is loaded
        if (btnMap) btnMap.classList.add('active');
        if (containerMap) containerMap.classList.remove('hidden');
        if (sidebarLocation) sidebarLocation.classList.remove('hidden');
        
        if (!leafletMap) {
            initLeafletMap();
        } else {
            leafletMap.setView([state.gpsLat, state.gpsLon], 19);
            setTimeout(() => {
                leafletMap.invalidateSize();
                if (centerMarker) {
                    centerMarker.setLatLng([state.gpsLat, state.gpsLon]);
                }
                drawMapPlan();
            }, 100);
        }
    }
}

function initThreeJS() {
    const container = document.getElementById('canvas-3d');
    container.innerHTML = ''; // Clean old sessions
    container.style.backgroundColor = state.show3DMap ? 'transparent' : '#0c0c10';
    
    const width = container.clientWidth;
    const height = container.clientHeight;
    
    // 1. Create Scene
    const scene = new THREE.Scene();
    scene.background = state.show3DMap ? null : new THREE.Color(0x0c0c10);
    state.three.scene = scene;
    
    // 2. Camera Setup
    const camera = new THREE.PerspectiveCamera(45, width / height, 0.1, 1000);
    camera.position.set(0, 18, 27); // Zoomed out a bit more on initial load
    state.three.camera = camera;
    
    // 3. Renderer Setup (enable alpha for transparent background)
    const renderer = new THREE.WebGLRenderer({ antialias: true, alpha: true });
    renderer.setSize(width, height);
    renderer.shadowMap.enabled = true;
    renderer.setClearColor(0x0c0c10, state.show3DMap ? 0 : 1);
    container.appendChild(renderer.domElement);
    state.three.renderer = renderer;
    
    // 4. Orbit Controls
    const controls = new THREE.OrbitControls(camera, renderer.domElement);
    controls.enableDamping = true;
    controls.dampingFactor = 0.05;
    controls.maxPolarAngle = Math.PI / 2 - 0.05; // Lock camera from dipping below ground level
    state.three.controls = controls;

    // Sync map toggle state on initialization
    const btn = document.getElementById('btn-3d-map-toggle');
    if (btn) {
        if (state.show3DMap) {
            btn.innerHTML = `<span class="material-icons" style="font-size: 14px;">map</span> Map Ground: ON`;
            btn.classList.add('active');
        } else {
            btn.innerHTML = `<span class="material-icons" style="font-size: 14px;">map</span> Map Ground: OFF`;
            btn.classList.remove('active');
        }
    }
    
    // 5. Ambient and Spot Lights
    const ambientLight = new THREE.AmbientLight(0xffffff, 0.6);
    scene.add(ambientLight);
    
    const dirLight = new THREE.DirectionalLight(0xffffff, 0.8);
    dirLight.position.set(20, 40, 20);
    dirLight.castShadow = true;
    scene.add(dirLight);
    
    // 6. Build the Floor plan geometry meshes
    build3DPlanMeshes(scene);
    build3DMapGround(scene);
    
    // 7. Animation Loop
    function animate() {
        state.three.animationFrameId = requestAnimationFrame(animate);
        
        if (state.three.isOrbiting && controls) {
            const target = controls.target;
            const dx = camera.position.x - target.x;
            const dz = camera.position.z - target.z;
            const radius = Math.sqrt(dx * dx + dz * dz);
            let angle = Math.atan2(dz, dx);
            angle += 0.003; // Smooth automatic orbit rotation speed
            
            camera.position.x = target.x + radius * Math.cos(angle);
            camera.position.z = target.z + radius * Math.sin(angle);
        }
        
        controls.update();
        renderer.render(scene, camera);
    }
    animate();
    
    // Handle container resizes
    const resizeObserver = new ResizeObserver(() => {
        if (!state.three.renderer) return;
        const w = container.clientWidth;
        const h = container.clientHeight;
        camera.aspect = w / h;
        camera.updateProjectionMatrix();
        renderer.setSize(w, h);
    });
    resizeObserver.observe(container);
}

// Extrudes and renders 3D elements base on 2D coordinates
function build3DPlanMeshes(scene) {
    // Determine bounds to center camera orbit anchor
    let sumX = 0, sumY = 0, vCount = state.vertices.length;
    if (vCount === 0) return;
    
    state.vertices.forEach(v => {
        sumX += v.x;
        sumY += v.y;
    });
    const centerX = sumX / vCount;
    const centerY = sumY / vCount;
    
    // Translate scene center to orbit controls anchor
    state.three.controls.target.set(centerX, 0, centerY);
    
    // 1. Grid/Floor plane helper
    const gridHelper = new THREE.GridHelper(50, 50, 0x6366f1, 0x222233);
    gridHelper.position.y = 0.005;
    state.three.gridHelper = gridHelper;
    if (!state.show3DMap) {
        scene.add(gridHelper);
    }
    
    // 2. Render Rooms (Floors)
    state.rooms.forEach(room => {
        const shape = new THREE.Shape();
        const startV = findVertex(room.vertices[0]);
        if (!startV) return;
        
        shape.moveTo(startV.x, startV.y);
        for (let i = 1; i < room.vertices.length; i++) {
            const v = findVertex(room.vertices[i]);
            shape.lineTo(v.x, v.y);
        }
        shape.closePath();
        
        // Extrude floor thickness slightly downwards
        const extrudeSettings = { depth: 0.05, bevelEnabled: false };
        const geometry = new THREE.ExtrudeGeometry(shape, extrudeSettings);
        
        // Hardwood texture style material
        const material = new THREE.MeshStandardMaterial({ 
            color: 0x312e81, // deep blue wood aesthetic
            roughness: 0.5,
            metalness: 0.1
        });
        
        const floorMesh = new THREE.Mesh(geometry, material);
        floorMesh.rotation.x = Math.PI / 2; // Flat on horizontal ground plane
        floorMesh.position.y = 0.0;
        scene.add(floorMesh);
    });
    
    // 3. Render Walls with Openings in 3D
    state.walls.forEach(w => {
        const v1 = findVertex(w.v1Id);
        const v2 = findVertex(w.v2Id);
        if (!v1 || !v2) return;
        
        const wallLength = Math.hypot(v2.x - v1.x, v2.y - v1.y);
        const wallAngle = Math.atan2(v2.y - v1.y, v2.x - v1.x);
        
        // Materials
        const isExterior = w.type.startsWith('exterior');
        const wallColor = isExterior ? 0xef4444 : 0x818cf8; // red brick style vs lavender interior
        const wallMaterial = new THREE.MeshStandardMaterial({ color: wallColor, roughness: 0.8 });
        
        // Sub-boxes generator to cutout door/window panels
        const wallOpenings = state.openings.filter(op => op.wallId === w.id);
        
        // Sort openings along wall offset
        wallOpenings.sort((a, b) => a.offset - b.offset);
        
        let prevOffset = 0;
        const subSegments = [];
        
        wallOpenings.forEach(op => {
            // Segment before the opening
            if (op.offset > prevOffset) {
                subSegments.push({
                    start: prevOffset,
                    end: op.offset,
                    bot: 0,
                    top: state.globalWallHeight,
                    type: 'solid'
                });
            }
            
            // Window bottom sill
            if (op.type === 'window' && op.sillHeight > 0) {
                subSegments.push({
                    start: op.offset,
                    end: op.offset + op.width,
                    bot: 0,
                    top: op.sillHeight,
                    type: 'solid'
                });
            }
            
            // Header beam above door / window
            const topHeader = op.sillHeight + op.height;
            if (topHeader < state.globalWallHeight) {
                subSegments.push({
                    start: op.offset,
                    end: op.offset + op.width,
                    bot: topHeader,
                    top: state.globalWallHeight,
                    type: 'solid'
                });
            }
            
            // Empty opening type (renders window glass frame or empty door)
            subSegments.push({
                start: op.offset,
                end: op.offset + op.width,
                bot: op.sillHeight,
                top: op.sillHeight + op.height,
                type: op.type, // 'door' or 'window'
                openingId: op.id
            });
            
            prevOffset = op.offset + op.width;
        });
        
        // Final solid wall segment
        if (wallLength > prevOffset) {
            subSegments.push({
                start: prevOffset,
                end: wallLength,
                bot: 0,
                top: state.globalWallHeight,
                type: 'solid'
            });
        }
        
        // Create 3D Meshes for all computed segments
        const wallGroup = new THREE.Group();
        
        subSegments.forEach(seg => {
            const segLen = seg.end - seg.start;
            if (segLen <= 0.001) return;
            
            if (seg.type === 'solid') {
                // Get local joint offsets for miter corners in 3D
                const joint1 = getWallJointPoints(w.id, w.v1Id);
                const joint2 = getWallJointPoints(w.id, w.v2Id);
                let localOffsets = null;
                
                if (joint1 && joint2) {
                    const dir = { x: Math.cos(wallAngle), y: Math.sin(wallAngle) };
                    const norm = { x: -dir.y, y: dir.x };
                    
                    localOffsets = {
                        v1: {
                            left: {
                                x: (joint1.left.x - v1.x) * dir.x + (joint1.left.y - v1.y) * dir.y,
                                z: (joint1.left.x - v1.x) * norm.x + (joint1.left.y - v1.y) * norm.y
                            },
                            right: {
                                x: (joint1.right.x - v1.x) * dir.x + (joint1.right.y - v1.y) * dir.y,
                                z: (joint1.right.x - v1.x) * norm.x + (joint1.right.y - v1.y) * norm.y
                            }
                        },
                        v2: {
                            left: {
                                x: (joint2.left.x - v1.x) * dir.x + (joint2.left.y - v1.y) * dir.y,
                                z: (joint2.left.x - v1.x) * norm.x + (joint2.left.y - v1.y) * norm.y
                            },
                            right: {
                                x: (joint2.right.x - v1.x) * dir.x + (joint2.right.y - v1.y) * dir.y,
                                z: (joint2.right.x - v1.x) * norm.x + (joint2.right.y - v1.y) * norm.y
                            }
                        }
                    };
                }

                let geom;
                if (localOffsets) {
                    // Start-Left
                    const xStartLeft = seg.start === 0 ? localOffsets.v1.left.x : seg.start;
                    const zStartLeft = seg.start === 0 ? localOffsets.v1.left.z : w.thickness / 2;

                    // End-Left
                    const xEndLeft = seg.end === wallLength ? localOffsets.v2.right.x : seg.end;
                    const zEndLeft = seg.end === wallLength ? localOffsets.v2.right.z : w.thickness / 2;

                    // End-Right
                    const xEndRight = seg.end === wallLength ? localOffsets.v2.left.x : seg.end;
                    const zEndRight = seg.end === wallLength ? localOffsets.v2.left.z : -w.thickness / 2;

                    // Start-Right
                    const xStartRight = seg.start === 0 ? localOffsets.v1.right.x : seg.start;
                    const zStartRight = seg.start === 0 ? localOffsets.v1.right.z : -w.thickness / 2;

                    const shape = new THREE.Shape();
                    shape.moveTo(xStartLeft, -zStartLeft);
                    shape.lineTo(xEndLeft, -zEndLeft);
                    shape.lineTo(xEndRight, -zEndRight);
                    shape.lineTo(xStartRight, -zStartRight);
                    shape.closePath();

                    const extrudeSettings = { depth: seg.top - seg.bot, bevelEnabled: false };
                    geom = new THREE.ExtrudeGeometry(shape, extrudeSettings);
                } else {
                    geom = new THREE.BoxGeometry(segLen, seg.top - seg.bot, w.thickness);
                }
                
                const mesh = new THREE.Mesh(geom, wallMaterial);
                if (localOffsets) {
                    mesh.rotation.x = -Math.PI / 2;
                    mesh.position.set(0, seg.bot, 0);
                } else {
                    mesh.position.set(
                        seg.start + segLen / 2, 
                        seg.bot + (seg.top - seg.bot) / 2, 
                        0
                    );
                }
                wallGroup.add(mesh);
            } 
            
            else if (seg.type === 'window') {
                // Faint cyan glass mesh for windows
                const geom = new THREE.BoxGeometry(segLen, seg.top - seg.bot, w.thickness * 0.5);
                const glassMaterial = new THREE.MeshStandardMaterial({
                    color: 0x06b6d4,
                    transparent: true,
                    opacity: 0.4,
                    roughness: 0.1
                });
                const mesh = new THREE.Mesh(geom, glassMaterial);
                mesh.position.set(seg.start + segLen/2, seg.bot + (seg.top - seg.bot)/2, 0);
                wallGroup.add(mesh);
            }
            
            else if (seg.type === 'door') {
                const op = findOpening(seg.openingId);
                const hinge = (op && op.hingeSide) || 'left';
                const swing = (op && op.swingDir) || 'out';
                
                // Open wooden panel
                const geom = new THREE.BoxGeometry(0.04, seg.top - seg.bot, segLen * 0.95);
                const woodMaterial = new THREE.MeshStandardMaterial({ color: 0x78350f, roughness: 0.7 });
                const mesh = new THREE.Mesh(geom, woodMaterial);
                
                // Position panel based on hinge side & swing direction
                const pivotX = hinge === 'left' ? seg.start : seg.end;
                const pivotZ = swing === 'out' ? (-segLen / 2) : (segLen / 2);
                
                mesh.position.set(pivotX, seg.bot + (seg.top - seg.bot)/2, pivotZ);
                wallGroup.add(mesh);
            }
        });
        
        // Rotate and align Wall Group to floor plan coordinate space
        wallGroup.position.set(v1.x, 0, v1.y);
        // Rotate local Z axis of ThreeJS wall group to match 2D segment line direction
        // In 3D: world Y is height, world X & Z are coordinates (x = 2D x, z = 2D y)
        wallGroup.rotation.y = -wallAngle; // Invert to match ThreeJS CCW rotations
        
        // Shift wall boxes so group rotation pivot is at start vertex center
        // By default Box geometry pivot is at its center, so we shift local coordinates:
        // Local x starts from 0 (pivot is 0), handled inside segment position setting: seg.start + segLen/2.
        
        scene.add(wallGroup);
    });
}

// --- Import / Export / Print Tools ---
function saveProject() {
    const dataStr = JSON.stringify({
        vertices: state.vertices,
        walls: state.walls,
        openings: state.openings,
        roomSettings: state.roomSettings,
        globalSettings: {
            height: state.globalWallHeight,
            extHeight: state.globalExteriorHeight,
            coverage: state.paintCoverage,
            wallCoats: state.wallCoats,
            ceilingCoats: state.ceilingCoats,
            method: state.applicationMethod,
            gpsLat: state.gpsLat,
            gpsLon: state.gpsLon,
            gpsRot: state.gpsRot,
            mapStyle: state.mapStyle
        }
    }, null, 2);
    
    const blob = new Blob([dataStr], { type: 'application/json' });
    const url = URL.createObjectURL(blob);
    
    const a = document.createElement('a');
    a.href = url;
    a.download = `paint-plan-${Date.now()}.json`;
    a.click();
    
    URL.revokeObjectURL(url);
}

function loadProject(e) {
    const file = e.target.files[0];
    if (!file) return;
    
    const reader = new FileReader();
    reader.onload = function(evt) {
        try {
            const data = JSON.parse(evt.target.result);
            
            state.vertices = data.vertices || [];
            state.walls = data.walls || [];
            state.openings = data.openings || [];
            state.roomSettings = data.roomSettings || {};
            
            if (data.globalSettings) {
                state.globalWallHeight = data.globalSettings.height || 2.4;
                state.globalExteriorHeight = data.globalSettings.extHeight || 2.8;
                state.paintCoverage = data.globalSettings.coverage || 10;
                state.wallCoats = data.globalSettings.wallCoats || 2;
                state.ceilingCoats = data.globalSettings.ceilingCoats || 2;
                state.applicationMethod = data.globalSettings.method || 'roller';
                state.gpsLat = data.globalSettings.gpsLat || -37.8136;
                state.gpsLon = data.globalSettings.gpsLon || 144.9631;
                state.gpsRot = data.globalSettings.gpsRot || 0;
                state.mapStyle = data.globalSettings.mapStyle || 'satellite';
                
                // Set form input displays
                document.getElementById('cfg-wall-height').value = state.globalWallHeight;
                document.getElementById('cfg-ext-height').value = state.globalExteriorHeight;
                document.getElementById('cfg-coverage').value = state.paintCoverage;
                document.getElementById('cfg-wall-coats').value = state.wallCoats;
                document.getElementById('cfg-ceil-coats').value = state.ceilingCoats;
                document.getElementById('cfg-method').value = state.applicationMethod;
                document.getElementById('cfg-gps-lat').value = state.gpsLat;
                document.getElementById('cfg-gps-lon').value = state.gpsLon;
                document.getElementById('cfg-gps-rot').value = state.gpsRot;
                document.getElementById('cfg-map-style').value = state.mapStyle;
                const valSpan = document.getElementById('cfg-gps-rot-val');
                if (valSpan) valSpan.innerText = `${state.gpsRot}°`;
            }
            
            deselectElement();
            recalculateAll();
            zoomToFit();
        } catch (err) {
            alert('Error loading file. Invalid project format.');
        }
    };
    reader.readAsText(file);
}

// Generate KML file for mapping coordinates (GPS simulation)
function exportKML() {
    if (state.walls.length === 0) {
        alert('Draw a plan first before exporting KML');
        return;
    }
    
    // Map local coordinates (meters) to geographic coordinates centered around standard GPS origin
    const refLat = state.gpsLat;
    const refLon = state.gpsLon;
    const refRotRad = (state.gpsRot * Math.PI) / 180;
    const metersPerDegreeLat = 111132;
    const metersPerDegreeLon = 111132 * Math.cos(refLat * Math.PI / 180);
    
    function toGPS(wx, wy) {
        // Rotate local coordinates clockwise relative to North
        const rx = wx * Math.cos(-refRotRad) - wy * Math.sin(-refRotRad);
        const ry = wx * Math.sin(-refRotRad) + wy * Math.cos(-refRotRad);
        return {
            lon: refLon + rx / metersPerDegreeLon,
            lat: refLat - ry / metersPerDegreeLat
        };
    }
    let kmlContent = `<?xml version="1.0" encoding="UTF-8"?>
<kml xmlns="http://www.opengis.net/kml/2.2">
  <Document>
    <name>Paint Plan - Geographic Scale</name>
    <Style id="wallStyle">
      <LineStyle>
        <color>ff0000ff</color>
        <width>4</width>
      </LineStyle>
      <PolyStyle>
        <color>80ff8080</color>
      </PolyStyle>
    </Style>
    <Style id="roomStyle">
      <PolyStyle>
        <color>7f50ff50</color>
      </PolyStyle>
    </Style>
`;

    // 1. Export walls as LineStrings
    state.walls.forEach(w => {
        const v1 = findVertex(w.v1Id);
        const v2 = findVertex(w.v2Id);
        const g1 = toGPS(v1.x, v1.y);
        const g2 = toGPS(v2.x, v2.y);
        
        kmlContent += `    <Placemark>
      <name>Wall ${w.id}</name>
      <styleUrl>#wallStyle</styleUrl>
      <LineString>
        <coordinates>
          ${g1.lon},${g1.lat},0
          ${g2.lon},${g2.lat},0
        </coordinates>
      </LineString>
    </Placemark>\n`;
    });
    
    // 2. Export Rooms as Extruded 3D Polygons
    state.rooms.forEach(room => {
        let coordStr = "";
        room.vertices.forEach(vId => {
            const v = findVertex(vId);
            const g = toGPS(v.x, v.y);
            coordStr += `          ${g.lon},${g.lat},${state.globalWallHeight}\n`;
        });
        
        // Close polygon loop
        const vStart = findVertex(room.vertices[0]);
        const gStart = toGPS(vStart.x, vStart.y);
        coordStr += `          ${gStart.lon},${gStart.lat},${state.globalWallHeight}`;
        
        kmlContent += `    <Placemark>
      <name>${room.name}</name>
      <styleUrl>#roomStyle</styleUrl>
      <Polygon>
        <extrude>1</extrude>
        <altitudeMode>relativeToGround</altitudeMode>
        <outerBoundaryIs>
          <LinearRing>
            <coordinates>
\n${coordStr}
            </coordinates>
          </LinearRing>
        </outerBoundaryIs>
      </Polygon>
    </Placemark>\n`;
    });
    
    kmlContent += `  </Document>
</kml>`;
    
    const blob = new Blob([kmlContent], { type: 'application/vnd.google-earth.kml+xml' });
    const url = URL.createObjectURL(blob);
    const a = document.createElement('a');
    a.href = url;
    a.download = `paint-plan-${Date.now()}.kml`;
    a.click();
    URL.revokeObjectURL(url);
}

function drawCornerAngles(wall) {
    if (!wall) return;
    const v1 = findVertex(wall.v1Id);
    const v2 = findVertex(wall.v2Id);
    if (!v1 || !v2) return;
    
    drawCornerAngleAtVertex(v1.id, wall.id);
    drawCornerAngleAtVertex(v2.id, wall.id);
}

function drawCornerAngleAtVertex(vId, activeWallId) {
    const v = findVertex(vId);
    if (!v) return;
    
    const meetingWalls = state.walls.filter(w => w.v1Id === vId || w.v2Id === vId);
    if (meetingWalls.length !== 2) return;
    
    const w1 = meetingWalls[0];
    const w2 = meetingWalls[1];
    
    const otherV1 = w1.v1Id === vId ? findVertex(w1.v2Id) : findVertex(w1.v1Id);
    const otherV2 = w2.v1Id === vId ? findVertex(w2.v2Id) : findVertex(w2.v1Id);
    if (!otherV1 || !otherV2) return;
    
    const ang1 = Math.atan2(otherV1.y - v.y, otherV1.x - v.x);
    const ang2 = Math.atan2(otherV2.y - v.y, otherV2.x - v.x);
    
    let diff = ang2 - ang1;
    while (diff < -Math.PI) diff += Math.PI * 2;
    while (diff > Math.PI) diff -= Math.PI * 2;
    
    let startAng = ang1;
    let endAng = ang2;
    if (diff < 0) {
        startAng = ang2;
        endAng = ang1;
        diff = -diff;
    }
    
    const deg = (diff * 180) / Math.PI;
    const sV = worldToScreen(v.x, v.y);
    const arcRadius = 40;
    
    ctx2D.save();
    ctx2D.strokeStyle = 'rgba(239, 68, 68, 0.75)';
    ctx2D.lineWidth = 1.5;
    ctx2D.beginPath();
    ctx2D.arc(sV.x, sV.y, arcRadius, startAng, endAng, false);
    ctx2D.stroke();
    
    const midAngle = startAng + diff / 2;
    const textDist = arcRadius + 15;
    const textX = sV.x + textDist * Math.cos(midAngle);
    const textY = sV.y + textDist * Math.sin(midAngle);
    
    ctx2D.fillStyle = '#ef4444';
    ctx2D.font = '600 11px Outfit, sans-serif';
    ctx2D.textAlign = 'center';
    ctx2D.textBaseline = 'middle';
    ctx2D.fillText(`${deg.toFixed(1)}°`, textX, textY);
    ctx2D.restore();
}

// --- Leaflet Map Alignment Engine ---
function initLeafletMap() {
    leafletMap = L.map('map-leaflet', {
        zoomControl: true,
        maxZoom: 21
    }).setView([state.gpsLat, state.gpsLon], 19);
    
    // Add open street map road tile layer
    L.tileLayer('https://{s}.tile.openstreetmap.org/{z}/{x}/{y}.png', {
        attribution: '&copy; <a href="https://www.openstreetmap.org/copyright">OpenStreetMap</a> contributors'
    }).addTo(leafletMap);
    
    mapLayersGroup = L.layerGroup().addTo(leafletMap);
    
    // Marker at center for repositioning
    centerMarker = L.marker([state.gpsLat, state.gpsLon], {
        draggable: true,
        title: "Drag to position plan"
    }).addTo(leafletMap);
    
    centerMarker.on('drag', (e) => {
        const latlng = e.target.getLatLng();
        state.gpsLat = latlng.lat;
        state.gpsLon = latlng.lng;
        
        document.getElementById('cfg-gps-lat').value = state.gpsLat.toFixed(6);
        document.getElementById('cfg-gps-lon').value = state.gpsLon.toFixed(6);
        
        drawMapPlan();
    });
    
    drawMapPlan();
}

function drawMapPlan() {
    if (!mapLayersGroup) return;
    mapLayersGroup.clearLayers();
    
    const refLat = state.gpsLat;
    const refLon = state.gpsLon;
    const refRotRad = (state.gpsRot * Math.PI) / 180;
    
    const metersPerDegreeLat = 111132;
    const metersPerDegreeLon = 111132 * Math.cos(refLat * Math.PI / 180);
    
    function toGPSMap(wx, wy) {
        // Rotate local coordinates clockwise around center marker
        const rx = wx * Math.cos(-refRotRad) - wy * Math.sin(-refRotRad);
        const ry = wx * Math.sin(-refRotRad) + wy * Math.cos(-refRotRad);
        return [
            refLat - ry / metersPerDegreeLat,
            refLon + rx / metersPerDegreeLon
        ];
    }
    
    // Draw Rooms
    state.rooms.forEach(room => {
        const latlngs = room.vertices.map(vId => {
            const v = findVertex(vId);
            return toGPSMap(v.x, v.y);
        });
        
        L.polygon(latlngs, {
            color: '#a855f7',
            fillColor: '#a855f7',
            fillOpacity: 0.35,
            weight: 2
        }).addTo(mapLayersGroup);
    });
    
    // Draw Walls
    state.walls.forEach(w => {
        const v1 = findVertex(w.v1Id);
        const v2 = findVertex(w.v2Id);
        if (!v1 || !v2) return;
        
        const pt1 = toGPSMap(v1.x, v1.y);
        const pt2 = toGPSMap(v2.x, v2.y);
        
        L.polyline([pt1, pt2], {
            color: w.type.startsWith('exterior') ? '#ef4444' : '#818cf8',
            weight: Math.max(3, w.thickness * 20),
            opacity: 0.8
        }).addTo(mapLayersGroup);
    });
}

// --- 3D Map Overlay Implementation ---
let map3DGroup = null;

function build3DMapGround(scene) {
    // Clean old map group
    if (map3DGroup) {
        scene.remove(map3DGroup);
        map3DGroup.traverse(child => {
            if (child.isMesh) {
                child.geometry.dispose();
                if (child.material) {
                    if (Array.isArray(child.material)) {
                        child.material.forEach(m => m.dispose());
                    } else {
                        child.material.dispose();
                    }
                }
            }
        });
        map3DGroup = null;
    }
    
    if (!state.show3DMap) return;
    
    map3DGroup = new THREE.Group();
    scene.add(map3DGroup);
    
    const refLat = state.gpsLat;
    const refLon = state.gpsLon;
    const zoom = 19; // high resolution zoom level
    
    const cosLat = Math.cos(refLat * Math.PI / 180);
    const metersPerDegreeLat = 111132;
    const metersPerDegreeLon = 111132 * cosLat;
    
    // Get center tile coords
    const centerTile = getTileCoords(refLat, refLon, zoom);
    
    // NW corner GPS helper
    function tileNW(tx, ty, z) {
        const numTiles = Math.pow(2, z);
        const lon = tx / numTiles * 360 - 180;
        const n = Math.PI - 2 * Math.PI * ty / numTiles;
        const lat = 180 / Math.PI * Math.atan(0.5 * (Math.exp(n) - Math.exp(-n)));
        return { lat, lon };
    }
    
    const loader = new THREE.TextureLoader();
    loader.crossOrigin = 'anonymous';
    
    const isSat = state.mapStyle === 'satellite';
    const satelliteUrl = 'https://mt1.google.com/vt/lyrs=s&x={x}&y={y}&z={z}';
    const streetUrl = 'https://tile.openstreetmap.org/{z}/{x}/{y}.png';
    const activeUrl = isSat ? satelliteUrl : streetUrl;
    
    // Build a 5x5 grid of map plane tiles
    for (let row = -2; row <= 2; row++) {
        for (let col = -2; col <= 2; col++) {
            const tx = centerTile.x + col;
            const ty = centerTile.y + row;
            
            const nw = tileNW(tx, ty, zoom);
            const se = tileNW(tx + 1, ty + 1, zoom);
            
            const nwX = (nw.lon - refLon) * metersPerDegreeLon;
            const nwY = (refLat - nw.lat) * metersPerDegreeLat;
            
            const seX = (se.lon - refLon) * metersPerDegreeLon;
            const seY = (refLat - se.lat) * metersPerDegreeLat;
            
            const tileW = seX - nwX;
            const tileH = seY - nwY;
            
            const geometry = new THREE.PlaneGeometry(tileW, tileH);
            
            const url = activeUrl
                .replace('{z}', zoom)
                .replace('{x}', tx)
                .replace('{y}', ty);
                
            const texture = loader.load(url, () => {
                if (state.three.renderer && state.three.camera) {
                    state.three.renderer.render(scene, state.three.camera);
                }
            });
            
            const material = new THREE.MeshBasicMaterial({
                map: texture,
                side: THREE.DoubleSide
            });
            
            const mesh = new THREE.Mesh(geometry, material);
            mesh.rotation.x = -Math.PI / 2; // Lay flat on horizontal plane
            mesh.position.set(nwX + tileW / 2, -0.01, nwY + tileH / 2); // slightly below 0 to avoid z-fighting
            
            map3DGroup.add(mesh);
        }
    }
    
    // Rotate map group counter-clockwise to match building's heading relative to North
    map3DGroup.rotation.y = -(state.gpsRot * Math.PI) / 180;
}

function getTileCoords(lat, lon, zoom) {
    const x = Math.floor((lon + 180) / 360 * Math.pow(2, zoom));
    const latRad = lat * Math.PI / 180;
    const y = Math.floor((1 - Math.log(Math.tan(latRad) + 1 / Math.cos(latRad)) / Math.PI) / 2 * Math.pow(2, zoom));
    return { x, y, z: zoom };
}

function toggle3DMapBackground() {
    state.show3DMap = !state.show3DMap;
    const btn = document.getElementById('btn-3d-map-toggle');
    const sidebarLocation = document.getElementById('sidebar-location-section');
    
    if (state.show3DMap) {
        btn.innerHTML = `<span class="material-icons" style="font-size: 14px;">map</span> Map Ground: ON`;
        btn.classList.add('active');
        if (sidebarLocation) sidebarLocation.classList.remove('hidden');
        
        const canvas3D = document.getElementById('canvas-3d');
        if (canvas3D) {
            canvas3D.style.backgroundColor = 'transparent';
        }
        
        // Hide grid helper
        if (state.three.scene && state.three.gridHelper) {
            state.three.scene.remove(state.three.gridHelper);
        }
        // Clear scene background to transparent
        if (state.three.scene) {
            state.three.scene.background = null;
        }
        if (state.three.renderer) {
            state.three.renderer.setClearColor(0x000000, 0);
        }
        
        // Rebuild map meshes in scene
        if (state.three.scene) {
            build3DMapGround(state.three.scene);
        }
    } else {
        btn.innerHTML = `<span class="material-icons" style="font-size: 14px;">map</span> Map Ground: OFF`;
        btn.classList.remove('active');
        if (sidebarLocation) sidebarLocation.classList.add('hidden');
        
        const canvas3D = document.getElementById('canvas-3d');
        if (canvas3D) {
            canvas3D.style.backgroundColor = '#0c0c10';
        }
        
        // Show grid helper
        if (state.three.scene && state.three.gridHelper) {
            state.three.scene.add(state.three.gridHelper);
        }
        // Restore scene background
        if (state.three.scene) {
            state.three.scene.background = new THREE.Color(0x0c0c10);
        }
        if (state.three.renderer) {
            state.three.renderer.setClearColor(0x0c0c10, 1);
        }
        
        // Discard map meshes
        if (state.three.scene) {
            build3DMapGround(state.three.scene);
        }
    }
}

let currentTileLayer2D = null;

function updateMapLayers() {
    const satelliteUrl = 'https://mt1.google.com/vt/lyrs=s&x={x}&y={y}&z={z}';
    const streetUrl = 'https://tile.openstreetmap.org/{z}/{x}/{y}.png';
    
    const isSat = state.mapStyle === 'satellite';
    const activeUrl = isSat ? satelliteUrl : streetUrl;
    const activeAttr = isSat ? 'Map data &copy; Google' : '&copy; OpenStreetMap';
    const maxNative = isSat ? 21 : 19;
    
    // Update 2D Map layer
    if (leafletMap) {
        if (currentTileLayer2D) {
            leafletMap.removeLayer(currentTileLayer2D);
        }
        currentTileLayer2D = L.tileLayer(activeUrl, {
            maxZoom: 22,
            maxNativeZoom: maxNative,
            attribution: activeAttr
        }).addTo(leafletMap);
    }
    
    // Update 3D Map meshes if scene is ready and visible
    if (state.three.scene && state.show3DMap) {
        build3DMapGround(state.three.scene);
    }
}

function initLeafletMap() {
    leafletMap = L.map('map-leaflet', {
        zoomControl: true,
        maxZoom: 22
    }).setView([state.gpsLat, state.gpsLon], 19);
    
    updateMapLayers();
    
    mapLayersGroup = L.layerGroup().addTo(leafletMap);
    
    // Marker at center for repositioning
    centerMarker = L.marker([state.gpsLat, state.gpsLon], {
        draggable: true,
        title: "Drag to position plan"
    }).addTo(leafletMap);
    
    centerMarker.on('drag', (e) => {
        const latlng = e.target.getLatLng();
        state.gpsLat = latlng.lat;
        state.gpsLon = latlng.lng;
        
        document.getElementById('cfg-gps-lat').value = state.gpsLat.toFixed(6);
        document.getElementById('cfg-gps-lon').value = state.gpsLon.toFixed(6);
        
        drawMapPlan();
    });
    
    setTimeout(() => {
        leafletMap.invalidateSize();
        drawMapPlan();
    }, 100);
}

function drawMapPlan() {
    if (!mapLayersGroup) return;
    mapLayersGroup.clearLayers();
    
    const refLat = state.gpsLat;
    const refLon = state.gpsLon;
    const refRotRad = (state.gpsRot * Math.PI) / 180;
    
    const metersPerDegreeLat = 111132;
    const metersPerDegreeLon = 111132 * Math.cos(refLat * Math.PI / 180);
    
    function toGPSMap(wx, wy) {
        // Rotate local coordinates clockwise around center marker
        const rx = wx * Math.cos(-refRotRad) - wy * Math.sin(-refRotRad);
        const ry = wx * Math.sin(-refRotRad) + wy * Math.cos(-refRotRad);
        return [
            refLat - ry / metersPerDegreeLat,
            refLon + rx / metersPerDegreeLon
        ];
    }
    
    // Draw Rooms
    state.rooms.forEach(room => {
        const latlngs = room.vertices.map(vId => {
            const v = findVertex(vId);
            return toGPSMap(v.x, v.y);
        });
        
        L.polygon(latlngs, {
            color: '#a855f7',
            fillColor: '#a855f7',
            fillOpacity: 0.35,
            weight: 2
        }).addTo(mapLayersGroup);
    });
    
    // Draw Walls
    state.walls.forEach(w => {
        const v1 = findVertex(w.v1Id);
        const v2 = findVertex(w.v2Id);
        if (!v1 || !v2) return;
        
        const pt1 = toGPSMap(v1.x, v1.y);
        const pt2 = toGPSMap(v2.x, v2.y);
        
        L.polyline([pt1, pt2], {
            color: w.type.startsWith('exterior') ? '#ef4444' : '#818cf8',
            weight: Math.max(3, w.thickness * 20),
            opacity: 0.8
        }).addTo(mapLayersGroup);
    });
}

function toggle3DOrbit() {
    state.three.isOrbiting = !state.three.isOrbiting;
    const btn = document.getElementById('btn-3d-orbit');
    if (btn) {
        if (state.three.isOrbiting) {
            btn.innerHTML = `<span class="material-icons" style="font-size: 14px;">autorenew</span> Auto Orbit: ON`;
            btn.classList.add('active');
        } else {
            btn.innerHTML = `<span class="material-icons" style="font-size: 14px;">autorenew</span> Auto Orbit: OFF`;
            btn.classList.remove('active');
        }
    }
}
